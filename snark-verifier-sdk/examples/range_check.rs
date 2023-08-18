use ark_std::{end_timer, start_timer};
use halo2_base::gates::builder::{
    BaseConfigParams, CircuitBuilderStage, GateThreadBuilder, RangeWithInstanceCircuitBuilder,
};
use halo2_base::gates::flex_gate::GateStrategy;
use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
use halo2_base::halo2_proofs::plonk::Circuit;
use halo2_base::safe_types::{GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::fs::gen_srs;

use itertools::Itertools;
use snark_verifier_sdk::halo2::aggregation::{AggregationConfigParams, VerifierUniversality};
use snark_verifier_sdk::SHPLONK;
use snark_verifier_sdk::{
    gen_pk,
    halo2::{aggregation::AggregationCircuit, gen_snark_shplonk},
    Snark,
};

fn generate_circuit(k: u32) -> Snark {
    let mut builder = GateThreadBuilder::new(false);
    let ctx = builder.main(0);
    let lookup_bits = k as usize - 1;
    let range = RangeChip::<Fr>::default(lookup_bits);

    let x = ctx.load_witness(Fr::from(14));
    range.range_check(ctx, x, 2 * lookup_bits + 1);
    range.gate().add(ctx, x, x);

    let circuit = RangeWithInstanceCircuitBuilder::<Fr>::keygen(
        builder.clone(),
        BaseConfigParams {
            strategy: GateStrategy::Vertical,
            k: k as usize,
            num_advice_per_phase: vec![1],
            num_lookup_advice_per_phase: vec![1],
            num_fixed: 1,
            lookup_bits: Some(lookup_bits),
        },
        vec![],
    );
    let params = gen_srs(k);

    let pk = gen_pk(&params, &circuit, None);
    let breakpoints = circuit.break_points();

    let circuit = RangeWithInstanceCircuitBuilder::<Fr>::prover(
        builder.clone(),
        circuit.params(),
        breakpoints,
        vec![],
    );
    gen_snark_shplonk(&params, &pk, circuit, None::<&str>)
}

fn main() {
    let dummy_snark = generate_circuit(13);

    let k = 14u32;
    let lookup_bits = k as usize - 1;
    let params = gen_srs(k);
    let mut agg_circuit = AggregationCircuit::new::<SHPLONK>(
        CircuitBuilderStage::Keygen,
        AggregationConfigParams { degree: k, lookup_bits, ..Default::default() },
        None,
        &params,
        vec![dummy_snark],
        VerifierUniversality::Full,
    );
    let agg_config = agg_circuit.config(Some(10));

    let start0 = start_timer!(|| "gen vk & pk");
    let pk = gen_pk(&params, &agg_circuit, None);
    end_timer!(start0);
    let break_points = agg_circuit.break_points();

    let snarks = (14..17).map(generate_circuit).collect_vec();
    for (i, snark) in snarks.into_iter().enumerate() {
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            agg_config,
            Some(break_points.clone()),
            &params,
            vec![snark],
            VerifierUniversality::Full,
        );
        let _snark = gen_snark_shplonk(&params, &pk, agg_circuit, None::<&str>);
        println!("snark {i} success");
    }
}
