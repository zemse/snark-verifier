use crate::{
    cost::{Cost, CostEstimation},
    loader::{native::NativeLoader, LoadedScalar, Loader},
    pcs::{self, AccumulationStrategy, PolynomialCommitmentScheme},
    util::{
        arithmetic::{CurveAffine, Field, Rotation},
        expression::{CommonPolynomial, CommonPolynomialEvaluation, LinearizationStrategy, Query},
        msm::Msm,
        transcript::TranscriptRead,
        Itertools,
    },
    verifier::PlonkVerifier,
    Error, Protocol,
};
use std::{collections::HashMap, iter, marker::PhantomData};

pub struct Plonk<AS>(PhantomData<AS>);

impl<C, L, PCS, AS> PlonkVerifier<C, L, PCS, AS> for Plonk<AS>
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
    AS: AccumulationStrategy<C, L, PCS>,
{
    type Proof = PlonkProof<C, L, PCS, AS>;

    fn read_proof<T>(
        protocol: &Protocol<C>,
        instances: &[Vec<L::LoadedScalar>],
        transcript: &mut T,
    ) -> Result<Self::Proof, Error>
    where
        T: TranscriptRead<C, L>,
    {
        PlonkProof::read(protocol, instances, transcript)
    }

    fn succint_verify(
        svk: &PCS::SuccinctVerifyingKey,
        protocol: &Protocol<C>,
        instances: &[Vec<L::LoadedScalar>],
        proof: &Self::Proof,
    ) -> Result<PCS::PreAccumulator, Error> {
        let common_poly_eval = {
            let mut common_poly_eval = CommonPolynomialEvaluation::new(
                &protocol.domain,
                langranges(protocol, instances),
                &proof.z,
            );

            L::LoadedScalar::batch_invert(common_poly_eval.denoms());
            common_poly_eval.evaluate();

            common_poly_eval
        };

        let mut evaluations = proof.evaluations(protocol, instances, &common_poly_eval);
        let commitments = proof.commitments(protocol, &common_poly_eval, &mut evaluations)?;
        let queries = proof.queries(protocol, evaluations);

        let mut accumulator =
            PCS::succinct_verify(svk, &commitments, &proof.z, &queries, &proof.pcs)?;

        for old_accumulator in proof.old_accumulators.iter() {
            accumulator += old_accumulator;
        }

        Ok(accumulator)
    }
}

#[derive(Clone, Debug)]
pub struct PlonkProof<C, L, PCS, AS>
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
    AS: AccumulationStrategy<C, L, PCS>,
{
    pub witnesses: Vec<L::LoadedEcPoint>,
    pub challenges: Vec<L::LoadedScalar>,
    pub quotients: Vec<L::LoadedEcPoint>,
    pub z: L::LoadedScalar,
    pub evaluations: Vec<L::LoadedScalar>,
    pub pcs: PCS::Proof,
    pub old_accumulators: Vec<(L::LoadedScalar, PCS::Accumulator)>,
    _marker: PhantomData<AS>,
}

impl<C, L, PCS, AS> PlonkProof<C, L, PCS, AS>
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
    AS: AccumulationStrategy<C, L, PCS>,
{
    fn read<T>(
        protocol: &Protocol<C>,
        instances: &[Vec<L::LoadedScalar>],
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        T: TranscriptRead<C, L>,
    {
        let loader = transcript.loader();
        if let Some(transcript_initial_state) = &protocol.transcript_initial_state {
            transcript.common_scalar(&loader.load_const(transcript_initial_state))?;
        }

        if protocol.num_instance
            != instances
                .iter()
                .map(|instances| instances.len())
                .collect_vec()
        {
            return Err(Error::InvalidInstances);
        }
        for instances in instances.iter() {
            for instance in instances.iter() {
                transcript.common_scalar(instance)?;
            }
        }

        let (witnesses, challenges) = {
            let (witnesses, challenges) = protocol
                .num_witness
                .iter()
                .zip(protocol.num_challenge.iter())
                .map(|(&n, &m)| {
                    Ok((
                        transcript.read_n_ec_points(n)?,
                        transcript.squeeze_n_challenges(m),
                    ))
                })
                .collect::<Result<Vec<_>, Error>>()?
                .into_iter()
                .unzip::<_, _, Vec<_>, Vec<_>>();

            (
                witnesses.into_iter().flatten().collect_vec(),
                challenges.into_iter().flatten().collect_vec(),
            )
        };

        let quotients = transcript.read_n_ec_points(protocol.quotient.num_chunk())?;

        let z = transcript.squeeze_challenge();
        let evaluations = transcript.read_n_scalars(protocol.evaluations.len())?;

        let pcs = PCS::read_proof(&protocol.domain, &Self::empty_queries(protocol), transcript)?;

        let old_accumulators = {
            let separators = transcript.squeeze_n_challenges(protocol.accumulator_indices.len());
            separators
                .into_iter()
                .zip(AS::extract_accumulators(
                    &protocol.accumulator_indices,
                    instances,
                )?)
                .collect_vec()
        };

        Ok(Self {
            witnesses,
            challenges,
            quotients,
            z,
            evaluations,
            pcs,
            old_accumulators,
            _marker: PhantomData,
        })
    }

    fn empty_queries(protocol: &Protocol<C>) -> Vec<pcs::Query<C::Scalar>> {
        protocol
            .queries
            .iter()
            .map(|query| pcs::Query {
                poly: query.poly,
                shift: protocol
                    .domain
                    .rotate_scalar(C::Scalar::one(), query.rotation),
                eval: (),
            })
            .collect()
    }

    fn queries(
        &self,
        protocol: &Protocol<C>,
        mut evaluations: HashMap<Query, L::LoadedScalar>,
    ) -> Vec<pcs::Query<C::Scalar, L::LoadedScalar>> {
        Self::empty_queries(protocol)
            .into_iter()
            .zip(
                protocol
                    .queries
                    .iter()
                    .map(|query| evaluations.remove(query).unwrap()),
            )
            .map(|(query, eval)| query.with_evaluation(eval))
            .collect()
    }

    fn commitments(
        &self,
        protocol: &Protocol<C>,
        common_poly_eval: &CommonPolynomialEvaluation<C, L>,
        evaluations: &mut HashMap<Query, L::LoadedScalar>,
    ) -> Result<Vec<Msm<C, L>>, Error> {
        let loader = common_poly_eval.zn().loader();
        let mut commitments = iter::empty()
            .chain(
                protocol
                    .preprocessed
                    .iter()
                    .map(|value| Msm::base(loader.ec_point_load_const(value))),
            )
            .chain(iter::repeat_with(Default::default).take(protocol.num_instance.len()))
            .chain(self.witnesses.iter().cloned().map(Msm::base))
            .collect_vec();

        let numerator = protocol.quotient.numerator.evaluate(
            &|scalar| Ok(Msm::constant(loader.load_const(&scalar))),
            &|poly| Ok(Msm::constant(common_poly_eval.get(poly).clone())),
            &|query| {
                evaluations
                    .get(&query)
                    .cloned()
                    .map(Msm::constant)
                    .or_else(|| {
                        (query.rotation == Rotation::cur())
                            .then_some(commitments.get(query.poly).cloned())
                            .flatten()
                    })
                    .ok_or(Error::InvalidQuery(query))
            },
            &|index| {
                self.challenges
                    .get(index)
                    .cloned()
                    .map(Msm::constant)
                    .ok_or(Error::InvalidChallenge(index))
            },
            &|a| Ok(-a?),
            &|a, b| Ok(a? + b?),
            &|a, b| {
                let (a, b) = (a?, b?);
                match (a.size(), b.size()) {
                    (0, _) => Ok(b * &a.try_into_constant().unwrap()),
                    (_, 0) => Ok(a * &b.try_into_constant().unwrap()),
                    (_, _) => Err(Error::InvalidLinearization),
                }
            },
            &|a, scalar| Ok(a? * &loader.load_const(&scalar)),
        )?;

        let quotient_query = Query::new(
            protocol.preprocessed.len() + protocol.num_instance.len() + self.witnesses.len(),
            Rotation::cur(),
        );
        let quotient = common_poly_eval
            .zn()
            .pow_const(protocol.quotient.chunk_degree as u64)
            .powers(self.quotients.len())
            .into_iter()
            .zip(self.quotients.iter().cloned().map(Msm::base))
            .map(|(coeff, chunk)| chunk * &coeff)
            .sum::<Msm<_, _>>();
        match protocol.linearization {
            Some(LinearizationStrategy::WithoutConstant) => {
                let linearization_query = Query::new(quotient_query.poly + 1, Rotation::cur());
                let (msm, constant) = numerator.split();
                commitments.push(quotient);
                commitments.push(msm);
                evaluations.insert(
                    quotient_query,
                    (constant.unwrap_or_else(|| loader.load_zero())
                        + evaluations.get(&linearization_query).unwrap())
                        * common_poly_eval.zn_minus_one_inv(),
                );
            }
            Some(LinearizationStrategy::MinusVanishingTimesQuotient) => {
                let (msm, constant) =
                    (numerator - quotient * common_poly_eval.zn_minus_one()).split();
                commitments.push(msm);
                evaluations.insert(
                    quotient_query,
                    constant.unwrap_or_else(|| loader.load_zero()),
                );
            }
            None => {
                commitments.push(quotient);
                evaluations.insert(
                    quotient_query,
                    numerator
                        .try_into_constant()
                        .ok_or(Error::InvalidLinearization)?
                        * common_poly_eval.zn_minus_one_inv(),
                );
            }
        }

        Ok(commitments)
    }

    fn evaluations(
        &self,
        protocol: &Protocol<C>,
        instances: &[Vec<L::LoadedScalar>],
        common_poly_eval: &CommonPolynomialEvaluation<C, L>,
    ) -> HashMap<Query, L::LoadedScalar> {
        let loader = common_poly_eval.zn().loader();
        let instance_evaluations = instances.iter().map(|instances| {
            loader.sum_products(
                &instances
                    .iter()
                    .enumerate()
                    .map(|(i, instance)| {
                        (
                            common_poly_eval.get(CommonPolynomial::Lagrange(i as i32)),
                            instance,
                        )
                    })
                    .collect_vec(),
            )
        });

        iter::empty()
            .chain(
                (protocol.preprocessed.len()..)
                    .zip(instance_evaluations)
                    .map(|(poly, eval)| (Query::new(poly, Rotation::cur()), eval)),
            )
            .chain(
                protocol
                    .evaluations
                    .iter()
                    .cloned()
                    .zip(self.evaluations.iter().cloned()),
            )
            .collect()
    }
}

impl<C, PCS, AS> CostEstimation<(C, PCS)> for Plonk<AS>
where
    C: CurveAffine,
    PCS: PolynomialCommitmentScheme<C, NativeLoader>
        + CostEstimation<C, Input = Vec<pcs::Query<C::Scalar>>>,
    AS: AccumulationStrategy<C, NativeLoader, PCS>,
{
    type Input = Protocol<C>;

    fn estimate_cost(protocol: &Protocol<C>) -> Cost {
        let plonk_cost = {
            let num_accumulator = protocol.accumulator_indices.len();
            let num_instance = protocol.num_instance.iter().sum();
            let num_commitment =
                protocol.num_witness.iter().sum::<usize>() + protocol.quotient.num_chunk();
            let num_evaluation = protocol.evaluations.len();
            let num_msm = protocol.preprocessed.len() + num_commitment + 1 + 2 * num_accumulator;
            Cost::new(num_instance, num_commitment, num_evaluation, num_msm)
        };
        let pcs_cost = {
            let queries = PlonkProof::<C, NativeLoader, PCS, AS>::empty_queries(protocol);
            PCS::estimate_cost(&queries)
        };
        plonk_cost + pcs_cost
    }
}

fn langranges<C, T>(protocol: &Protocol<C>, instances: &[Vec<T>]) -> impl IntoIterator<Item = i32>
where
    C: CurveAffine,
{
    protocol
        .quotient
        .numerator
        .used_langrange()
        .into_iter()
        .chain(
            0..instances
                .iter()
                .map(|instance| instance.len())
                .max()
                .unwrap_or_default() as i32,
        )
}
