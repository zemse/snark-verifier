#![feature(associated_type_defaults)]
#![feature(trait_alias)]
#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_base::halo2_proofs::{self};
use halo2_proofs::{
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        group::ff::Field,
    },
    plonk::{keygen_pk, keygen_vk, Circuit, ProvingKey, Selector},
    poly::kzg::commitment::ParamsKZG,
    SerdeFormat,
};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
pub use snark_verifier::loader::native::NativeLoader;
use snark_verifier::{
    pcs::kzg::{Bdfg21, Gwc19, KzgAs, LimbsEncoding},
    verifier::{self, plonk::PlonkProtocol},
};
use std::{
    fs::{self, File},
    io::{self, BufReader, BufWriter},
    path::Path,
};

pub use snark_verifier;

#[cfg(feature = "loader_evm")]
pub mod evm;
#[cfg(feature = "loader_halo2")]
pub mod halo2;

pub const LIMBS: usize = 3;
pub const BITS: usize = 88;

const BUFFER_SIZE: usize = 1024 * 1024; // 1MB

/// AS stands for accumulation scheme.
/// AS can be either `Kzg<Bn256, Gwc19>` (the original PLONK KZG multi-open) or `Kzg<Bn256, Bdfg21>` (SHPLONK)
pub type PlonkVerifier<AS> = verifier::plonk::PlonkVerifier<AS, LimbsEncoding<LIMBS, BITS>>;
pub type PlonkSuccinctVerifier<AS> =
    verifier::plonk::PlonkSuccinctVerifier<AS, LimbsEncoding<LIMBS, BITS>>;
pub type SHPLONK = KzgAs<Bn256, Bdfg21>;
pub type GWC = KzgAs<Bn256, Gwc19>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Snark {
    pub protocol: PlonkProtocol<G1Affine>,
    pub instances: Vec<Vec<Fr>>,
    pub proof: Vec<u8>,
}

impl Snark {
    pub fn new(protocol: PlonkProtocol<G1Affine>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> Self {
        Self { protocol, instances, proof }
    }

    pub fn proof(&self) -> &[u8] {
        &self.proof[..]
    }
}

pub trait CircuitExt<F: Field>: Circuit<F> {
    /// Return the number of instances of the circuit.
    /// This may depend on extra circuit parameters but NOT on private witnesses.
    fn num_instance(&self) -> Vec<usize>;

    fn instances(&self) -> Vec<Vec<F>>;

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        None
    }

    /// Output the simple selector columns (before selector compression) of the circuit
    fn selectors(_: &Self::Config) -> Vec<Selector> {
        vec![]
    }
}

pub fn read_pk<C: Circuit<Fr>>(path: &Path, params: C::Params) -> io::Result<ProvingKey<G1Affine>> {
    read_pk_with_capacity::<C>(BUFFER_SIZE, path, params)
}

pub fn read_pk_with_capacity<C: Circuit<Fr>>(
    capacity: usize,
    path: impl AsRef<Path>,
    params: C::Params,
) -> io::Result<ProvingKey<G1Affine>> {
    let f = File::open(path.as_ref())?;
    #[cfg(feature = "display")]
    let read_time = start_timer!(|| format!("Reading pkey from {:?}", path.as_ref()));

    // BufReader is indeed MUCH faster than Read
    let mut bufreader = BufReader::with_capacity(capacity, f);
    // But it's even faster to load the whole file into memory first and then process,
    // HOWEVER this requires twice as much memory to initialize
    // let initial_buffer_size = f.metadata().map(|m| m.len() as usize + 1).unwrap_or(0);
    // let mut bufreader = Vec::with_capacity(initial_buffer_size);
    // f.read_to_end(&mut bufreader)?;
    let pk =
        ProvingKey::read::<_, C>(&mut bufreader, SerdeFormat::RawBytesUnchecked, params).unwrap();

    #[cfg(feature = "display")]
    end_timer!(read_time);

    Ok(pk)
}

#[allow(clippy::let_and_return)]
pub fn gen_pk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>, // TODO: read pk without params
    circuit: &C,
    path: Option<&Path>,
) -> ProvingKey<G1Affine> {
    if let Some(path) = path {
        if let Ok(pk) = read_pk::<C>(path, circuit.params()) {
            return pk;
        }
    }
    #[cfg(feature = "display")]
    let pk_time = start_timer!(|| "Generating vkey & pkey");

    let vk = keygen_vk(params, circuit).unwrap();
    let pk = keygen_pk(params, vk, circuit).unwrap();

    #[cfg(feature = "display")]
    end_timer!(pk_time);

    if let Some(path) = path {
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| format!("Writing pkey to {path:?}"));

        path.parent().and_then(|dir| fs::create_dir_all(dir).ok()).unwrap();
        let mut f = BufWriter::with_capacity(BUFFER_SIZE, File::create(path).unwrap());
        pk.write(&mut f, SerdeFormat::RawBytesUnchecked).unwrap();

        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    pk
}

pub fn read_instances(path: impl AsRef<Path>) -> Result<Vec<Vec<Fr>>, bincode::Error> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);
    let instances: Vec<Vec<[u8; 32]>> = bincode::deserialize_from(reader)?;
    instances
        .into_iter()
        .map(|instance_column| {
            instance_column
                .iter()
                .map(|bytes| {
                    Option::from(Fr::from_bytes(bytes)).ok_or(Box::new(bincode::ErrorKind::Custom(
                        "Invalid finite field point".to_owned(),
                    )))
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect()
}

pub fn write_instances(instances: &[&[Fr]], path: impl AsRef<Path>) {
    let instances: Vec<Vec<[u8; 32]>> = instances
        .iter()
        .map(|instance_column| instance_column.iter().map(|x| x.to_bytes()).collect_vec())
        .collect_vec();
    let f = BufWriter::new(File::create(path).unwrap());
    bincode::serialize_into(f, &instances).unwrap();
}

#[cfg(feature = "zkevm")]
mod zkevm {
    use super::CircuitExt;
    use eth_types::Field;
    use zkevm_circuits::{evm_circuit::EvmCircuit, state_circuit::StateCircuit};

    impl<F: Field> CircuitExt<F> for EvmCircuit<F> {
        fn instances(&self) -> Vec<Vec<F>> {
            vec![]
        }
        fn num_instance(&self) -> Vec<usize> {
            vec![]
        }
    }

    impl<F: Field> CircuitExt<F> for StateCircuit<F> {
        fn instances(&self) -> Vec<Vec<F>> {
            vec![]
        }
        fn num_instance(&self) -> Vec<usize> {
            vec![]
        }
    }
}
