use crate::{
    loader::halo2::test::MainGateWithRange,
    system::halo2::test::read_or_create_srs,
    util::arithmetic::{fe_to_limbs, CurveAffine, MultiMillerLoop},
};
use halo2_proofs::poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

mod native;

#[cfg(feature = "loader_evm")]
mod evm;

#[cfg(feature = "loader_halo2")]
mod halo2;

pub const TESTDATA_DIR: &str = "./src/system/halo2/test/kzg/testdata";

pub const LIMBS: usize = 4;
pub const BITS: usize = 68;

pub fn setup<M: MultiMillerLoop>(k: u32) -> ParamsKZG<M> {
    ParamsKZG::<M>::setup(k, ChaCha20Rng::from_seed(Default::default()))
}

pub fn main_gate_with_range_with_mock_kzg_accumulator<M: MultiMillerLoop>(
) -> MainGateWithRange<M::Scalar> {
    let srs = read_or_create_srs(TESTDATA_DIR, 1, setup::<M>);
    let [g1, s_g1] = [srs.get_g()[0], srs.get_g()[1]].map(|point| point.coordinates().unwrap());
    MainGateWithRange::new(
        [*s_g1.x(), *s_g1.y(), *g1.x(), *g1.y()]
            .iter()
            .cloned()
            .flat_map(fe_to_limbs::<_, _, LIMBS, BITS>)
            .collect(),
    )
}

macro_rules! halo2_kzg_config {
    ($zk:expr, $num_proof:expr) => {
        $crate::system::halo2::Config {
            zk: $zk,
            query_instance: false,
            num_instance: Vec::new(),
            num_proof: $num_proof,
            accumulator_indices: None,
        }
    };
    ($zk:expr, $num_proof:expr, $accumulator_indices:expr) => {
        $crate::system::halo2::Config {
            zk: $zk,
            query_instance: false,
            num_instance: Vec::new(),
            num_proof: $num_proof,
            accumulator_indices: Some($accumulator_indices),
        }
    };
}

macro_rules! halo2_kzg_prepare {
    ($k:expr, $config:expr, $create_circuit:expr) => {{
        use halo2_curves::bn256::Bn256;
        use $crate::system::halo2::test::{
            halo2_prepare,
            kzg::{setup, TESTDATA_DIR},
        };

        halo2_prepare!(TESTDATA_DIR, $k, setup::<Bn256>, $config, $create_circuit)
    }};
}

macro_rules! halo2_kzg_create_snark {
    (
        $prover:ty,
        $verifier:ty,
        $verification_strategy:ty,
        $transcript_read:ty,
        $transcript_write:ty,
        $encoded_challenge:ty,
        $params:expr,
        $pk:expr,
        $protocol:expr,
        $circuits:expr
    ) => {{
        use halo2_proofs::poly::kzg::commitment::KZGCommitmentScheme;
        use $crate::system::halo2::test::halo2_create_snark;

        halo2_create_snark!(
            KZGCommitmentScheme<_>,
            $prover,
            $verifier,
            $verification_strategy,
            $transcript_read,
            $transcript_write,
            $encoded_challenge,
            $params,
            $pk,
            $protocol,
            $circuits
        )
    }};
}

macro_rules! halo2_kzg_native_verify {
    (
        $plonk_verifier:ty,
        $params:expr,
        $protocol:expr,
        $instances:expr,
        $transcript:expr
    ) => {{
        use $crate::system::halo2::test::halo2_native_verify;

        halo2_native_verify!(
            $plonk_verifier,
            $params,
            $protocol,
            $instances,
            $transcript,
            &$params.get_g()[0],
            &($params.g2(), $params.s_g2())
        )
    }};
}

pub(crate) use {
    halo2_kzg_config, halo2_kzg_create_snark, halo2_kzg_native_verify, halo2_kzg_prepare,
};
