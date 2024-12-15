#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

mod permissible;
mod select;
mod generator;
mod bases;

use bases::{OrchardFixedBases, OrchardFixedBasesFull};
use ff::{Field, PrimeField};
use halo2_gadgets::ecc::chip::FixedPoint;
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::pasta::{pallas, EqAffine, Fp, Fq};
use halo2_proofs::plonk::{
    self, create_proof, keygen_pk, keygen_vk, verify_proof, BatchVerifier,
    Circuit, ConstraintSystem, Error, SingleVerifier,
};
use halo2_gadgets::ecc::{
        chip::{EccChip, EccConfig},
        ScalarFixed      
};
use halo2_gadgets::ecc::{FixedPoint as FPoint, Point};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use halo2_proofs::{circuit::*, plonk::*};
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::group::Group;
use pasta_curves::{vesta, Ep, EpAffine};
use rand_core::OsRng;
use rand::Rng;
use std::time::Instant;
use pasta_curves::group::Curve;
use permissible::*;
use select::*;
use generator::*;
use halo2_proofs::dev::MockProver;


/// This represents an advice column at a certain row in the ConstraintSystem
#[derive(Debug, Clone)]
struct MyConfig {
    pub select: SelectConfig,
    pub permisable: PrmsConfig,
    pub ecc_config: Vec<EccConfig<OrchardFixedBases>>,
    pub instance: Column<Instance>,
}

#[derive(Default, Clone, Debug)]
struct MyCircuit {
    pub commits_x: Vec<Value<Fp>>,
    pub commits_y: Vec<Value<Fp>>,
    pub witness: Value<Fp>,
    pub w_sqrt: Value<Fp>,
    pub rerand_scalar: Value<Fq>,
    pub k: usize,
    pub index: usize,
    pub msm_scalars: Vec<Value<Fq>>
}

impl Circuit<Fp> for MyCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        MyChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let config_clone = config.clone();
        let chip = MyChip::construct(config_clone.select, config_clone.permisable, config.clone());
        chip.assign_select(
            layouter.namespace(|| "select"),
            &self.commits_x,
            &self.witness,
            self.k,
        );

        chip.assign_perm(
            layouter.namespace(|| "permissible"),
            &self.commits_x,
            &self.commits_y,
            &self.w_sqrt,
            self.index,
        );

        let mut ecc_chip = vec![];
        for conf in config.ecc_config.iter() {
            ecc_chip.push(EccChip::construct(conf.clone()));
        }
        chip.assign_rerand(layouter.namespace(|| "rerand"), ecc_chip[0].clone(), self.rerand_scalar, self.commits_x[self.index], self.commits_y[self.index]);
        
        let bases = vec![
            OrchardFixedBasesFull::gens_1,
            OrchardFixedBasesFull::gens_2,
            OrchardFixedBasesFull::gens_3,
            OrchardFixedBasesFull::gens_4,
            OrchardFixedBasesFull::gens_5,
            OrchardFixedBasesFull::gens_6,
            OrchardFixedBasesFull::gens_7,
            OrchardFixedBasesFull::gens_8,
            OrchardFixedBasesFull::gens_9,
            OrchardFixedBasesFull::gens_10,
            OrchardFixedBasesFull::gens_11,
            OrchardFixedBasesFull::gens_12,
            OrchardFixedBasesFull::gens_13,
            OrchardFixedBasesFull::gens_14,
            OrchardFixedBasesFull::gens_15,
            OrchardFixedBasesFull::gens_16,
            ];
        chip.assign_msm(layouter.namespace(|| "msm"), ecc_chip.clone(), self.msm_scalars.clone(), bases);

        Ok(())
    }
}

struct MyChip {
    select: SelectChip,
    permisable: PrmsChip,
    config: MyConfig
}

impl MyChip {
    fn construct(s_config: SelectConfig, p_config: PrmsConfig, config: MyConfig) -> Self {
        Self {
            select: SelectChip::construct(s_config),
            permisable: PrmsChip::construct(p_config),
            config,
        }
    }

    fn configure(meta: &mut plonk::ConstraintSystem<Fp>) -> MyConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let col_d = meta.advice_column();
        let select_config = SelectChip::configure(meta, vec![col_a, col_b, col_c]);
        let prms_config = PrmsChip::configure(meta, vec![col_a, col_b, col_d]);

        let mut ecc_config = vec![];
        for i in 0..33 {
            let advices = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),

            ];    

            for advice in advices.iter() {
                meta.enable_equality(*advice);
            }
    
            let lagrange_coeffs = [
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
            ];
    
            meta.enable_constant(lagrange_coeffs[0]);
    
            let table_idx = meta.lookup_table_column();
            let range_check = LookupRangeCheckConfig::configure(meta, advices[9], table_idx);
    
            let conf =
            EccChip::<OrchardFixedBases>::configure(meta, advices, lagrange_coeffs, range_check);    
            ecc_config.push(conf);
        }
        

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        MyConfig {
            select: select_config,
            permisable: prms_config,
            ecc_config,
            instance
        }
    }

    pub fn assign_select(
        &self,
        layouter: impl Layouter<Fp>,
        x: &Vec<Value<Fp>>,
        witness: &Value<Fp>,
        num_rows: usize,
    ) {
        SelectChip::assign(&self.select, layouter, x, witness, num_rows).expect("Select assignment Error");
    }

    //Soundness issue: reassigning row
    pub fn assign_perm( 
        &self,
        layouter: impl Layouter<Fp>,
        x: &Vec<Value<Fp>>,
        y: &Vec<Value<Fp>>,
        y_sqrt: &Value<Fp>,
        index: usize,
    ) {
        PrmsChip::assign(&self.permisable, layouter, &x[index], &y[index], y_sqrt).expect("Permisiible assignment Error");
    }

    pub fn assign_rerand(
        &self,
        mut layouter: impl Layouter<Fp>,
        ecc_chip: EccChip<OrchardFixedBases>,
        rerand_scalar: Value<Fq>,
        x_child: Value<Fp>,
        y_child: Value<Fp>,
    )
    {   
        let scalar = ScalarFixed::new(
            ecc_chip.clone(),
            layouter.namespace(|| "scalar"),
            rerand_scalar,
        ).expect("Couldn't witness scalar");

        let value_commit_r = OrchardFixedBasesFull::ValueCommitR;
        let value_commit_r = FPoint::from_inner(ecc_chip.clone(), value_commit_r);
        let res = value_commit_r.mul(
            layouter.namespace(|| "rerand_scalar mul"), 
            scalar
        ).expect("Multiplication failed");

        let mut tmp_x = Fp::zero();
        x_child.map(|v| tmp_x = v);
        let mut tmp_y = Fp::zero();
        y_child.map(|v| tmp_y = v);
        let tmp = EpAffine::from_xy(tmp_x, tmp_y).expect("Couldn't construct point from x,y");

        let pt = Point::new(
            ecc_chip, 
            layouter.namespace(|| "witness non identity point"), 
            Value::known(tmp),
        ).expect("Couldn't witness a Point");

        let rerand = res.0.add(
            layouter.namespace(|| "rerandomized commitment"), 
            &pt).expect("Couldn't perform addition");
        
        layouter.constrain_instance(rerand.inner().x().cell(), self.config.instance, 0).expect("Couldn't constrain instance");
        layouter.constrain_instance(rerand.inner().y().cell(), self.config.instance, 1).expect("Couldn't constrain instance");

    }

    pub fn assign_msm(
        &self,
        mut layouter: impl Layouter<Fp>,
        ecc_chip: Vec<EccChip<OrchardFixedBases>>,
        msm_scalars: Vec<Value<Fq>>,
        bases: Vec<OrchardFixedBasesFull>
    )
    {
        let scalar = ScalarFixed::new(
            ecc_chip[0].clone(),
            layouter.namespace(|| "scalar"),
            msm_scalars[0],
        ).expect("Couldn't witness scalar");

        let value_commit_r = FPoint::from_inner(ecc_chip[0].clone(), bases[0]);
        let mut res = value_commit_r.mul(
            layouter.namespace(|| "rerand_scalar mul"), 
            scalar
        ).expect("Multiplication failed").0;

        for i in 1..64 {
            let scalar = ScalarFixed::new(
                ecc_chip[(i+1)/2].clone(),
                layouter.namespace(|| "scalar"),
                msm_scalars[i],
            ).expect("Couldn't witness scalar");

            let value_commit = FPoint::from_inner(ecc_chip[(i+1)/2].clone(), bases[i%2]);
            let new_pt = value_commit.mul(
                layouter.namespace(|| "rerand_scalar mul"), 
                scalar
            ).expect("Multiplication failed").0;


            res = res.add(layouter.namespace(|| "Addition"), &new_pt).expect("msg");
        }

        layouter.constrain_instance(res.inner().x().cell(), self.config.instance, 2).expect("Couldn't constrain instance");
        layouter.constrain_instance(res.inner().y().cell(), self.config.instance, 3).expect("Couldn't constrain instance");
    }
}

fn keygen(k: u32, empty_circuit: MyCircuit) -> (Params<EqAffine>, ProvingKey<EqAffine>) {
    let params: Params<EqAffine> = Params::new(k);
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");
    (params, pk)
}

fn prover(
    params: &Params<EqAffine>,
    pk: &ProvingKey<EqAffine>,
    circuit: MyCircuit,
    public_input: &[&[Fp]],
) -> Vec<u8> {
    let rng = OsRng;
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(params, pk, &[circuit], &[public_input], rng, &mut transcript)
        .expect("proof generation should not fail");
    transcript.finalize()
}

fn verifier(
    params: &Params<EqAffine>, 
    vk: &VerifyingKey<EqAffine>, 
    proof: &[u8], 
    public_input: &[&[Fp]],
    ) {
    let strategy = SingleVerifier::new(params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof);
    assert!(verify_proof(params, vk, strategy, &[public_input], &mut transcript).is_ok());
}

fn main() {
    let k = 8;
    let depth = 4;
    println!("k = {}", k-4);
    println!("depth = {depth}");
    let index = 2;

    let iterations = 1 << (k-4);

    let hasher = pallas::Point::hash_to_curve("CT_COMMITMENT");
    let mut commitments: Vec<pallas::Point> = Vec::with_capacity(iterations);
    let bases = vec![
        OrchardFixedBasesFull::gens_1,
        OrchardFixedBasesFull::gens_2,
        OrchardFixedBasesFull::gens_3,
        OrchardFixedBasesFull::gens_4,
        OrchardFixedBasesFull::gens_5,
        OrchardFixedBasesFull::gens_6,
        OrchardFixedBasesFull::gens_7,
        OrchardFixedBasesFull::gens_8,
        OrchardFixedBasesFull::gens_9,
        OrchardFixedBasesFull::gens_10,
        OrchardFixedBasesFull::gens_11,
        OrchardFixedBasesFull::gens_12,
        OrchardFixedBasesFull::gens_13,
        OrchardFixedBasesFull::gens_14,
        OrchardFixedBasesFull::gens_15,
        OrchardFixedBasesFull::gens_16,
        ];


    for _ in 0..iterations {
        let mut my_array: [u8; 11] = [0; 11];

        let mut rng = rand::thread_rng();
        for i in 0..11 {
            my_array[i] = rng.gen();
        }
        let c = hasher(&my_array);
        let (c, _) = permissible_commitment(&c, &pallas::Point::generator());
        commitments.push(c);
    }

    let mut parent = pallas::Point::identity();
    let mut scalars: Vec<Value<pallas::Scalar>> = Vec::with_capacity(iterations);

    for i in  0..iterations {
        let mut my_array: [u64; 4] = [0; 4];

        let mut rng = rand::thread_rng();
        for j in 0..4 {
            my_array[j] = rng.gen();
        }
        scalars.push(Value::known(pallas::Scalar::from_raw(my_array)));
        let base = OrchardFixedBasesFull::generator(&bases[i%2]);
        parent += Ep::from(base) * pallas::Scalar::from_raw(my_array);
    }

    let (p_c, _) = permissible_commitment(&parent, &pallas::Point::generator());
    commitments[index] = p_c;

    let mut commitments_x: Vec<Value<Fp>> = Vec::with_capacity(iterations);

    for i in 0..iterations {
        let pt = commitments[i].to_affine().coordinates().expect("Couldn't get coordinates of a point"); 
        commitments_x.push(Value::known(*pt.x()));
    }

    let mut commitments_y: Vec<Value<Fp>> = Vec::with_capacity(iterations);

    for i in 0..iterations {
        let pt = commitments[i].to_affine().coordinates().expect("Couldn't get coordinates of a point"); 
        commitments_y.push(Value::known(*pt.y()));
    }

    let witness = commitments_x[index].clone();
    let witness_y = commitments_y[index].clone();
    let gen = OrchardFixedBasesFull::generator(&OrchardFixedBasesFull::ValueCommitR);
    let generator = Ep::from(gen);
    let rerand_scalar = pallas::Scalar::from_raw([1, 2, 3, 4]);
    let rerand_pt = commitments[index].clone() + generator * rerand_scalar;
    let rerand_scalar = Value::known(rerand_scalar);
    let w_sqrt: Value<Option<Fp>> = witness_y.map(|v| v.sqrt().into());
    let w_sqrt = w_sqrt.map(|opt_fp| opt_fp.unwrap_or_default());


    let circuit = MyCircuit {
        commits_x: commitments_x,
        commits_y: commitments_y,
        witness,
        w_sqrt,
        rerand_scalar,
        k: iterations,
        msm_scalars: scalars,
        index,

    };

    let mut commitments_x: Vec<Value<Fp>> = Vec::with_capacity(iterations);

    for _ in 0..iterations {
        commitments_x.push(Value::unknown());
    }

    let mut commitments_y: Vec<Value<Fp>> = Vec::with_capacity(iterations);

    for _ in 0..iterations {
        commitments_y.push(Value::unknown());
    }
    let mut scalars: Vec<Value<pallas::Scalar>> = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        scalars.push(Value::unknown());
    }

    let witness = Value::unknown();
    let scalar: Value<Fq> = Value::unknown();

    let empty_circuit = MyCircuit {
        commits_x: commitments_x,
        commits_y: commitments_y,
        witness: witness,
        w_sqrt: witness,
        rerand_scalar: scalar,
        k: iterations,
        msm_scalars: scalars,
        index,
    };

    let tmp = (rerand_pt).to_affine().coordinates().expect("Couldn't get coordinates of a point"); 
    let parent_pt = parent.to_affine().coordinates().expect("Couldn't get coordinates of a point"); 
    let public_input = &[*tmp.x(), *tmp.y(), *parent_pt.x(), *parent_pt.y()];
    // let public_input = vec![*tmp.x(), *tmp.y(), *parent_pt.x(), *parent_pt.y()];
    

    // let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    // prover.assert_satisfied();

    let start_time = Instant::now();
    let (params, pk) = keygen(k, empty_circuit.clone());
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed keygen time: {:?}ms", elapsed_time.as_millis());

    let start_time = Instant::now();
    let proof = prover(&params, &pk, circuit, &[public_input]);
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed prover time: {:?}ms", elapsed_time.as_millis()*depth);
    let proof_size = proof.len() as f64 / 1024.;
    println!("Proof size is {}kb", (depth as f64)*proof_size);

    // let start_time = Instant::now();
    // verifier(&params, pk.get_vk(), &proof, &[public_input]);
    // let end_time = Instant::now();
    // let elapsed_time = end_time.duration_since(start_time);
    // println!("Elapsed verifier time: {:?}ms", elapsed_time.as_millis());

    let mut batch: BatchVerifier<EqAffine> = BatchVerifier::new();
    for _ in 0..depth*1 {
        batch.add_proof(vec![vec![vec![*tmp.x(), *tmp.y(), *parent_pt.x(), *parent_pt.y()]]], proof.clone());
    }

    let start_time = Instant::now();
    assert!(batch.finalize(&params, pk.get_vk()));
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!(
        "Elapsed verifier time: {:?}ms",
        elapsed_time.as_millis()
    );
}
