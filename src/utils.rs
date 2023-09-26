use halo2_base::QuantumCell::Constant;
use halo2_base::halo2_proofs::dev::metadata::Gate;
use halo2_base::{
    gates::{GateInstructions, GateChip, RangeChip, RangeInstructions},
    utils::ScalarField,
    AssignedValue, Context,
};
use itertools::Itertools;

const NUM_HASH_VALUES: usize = 8;
    
pub const NUM_ROUNDS: usize = 64;
const ROUND_CONSTANTS: [u32; NUM_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
];
pub const INIT_HASH_VALUES: [u32; NUM_HASH_VALUES] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
];


fn xor<F: ScalarField>(
    gate: &GateChip<F>,
    ctx: &mut Context<F>,
    a: AssignedValue<F>,
    b: AssignedValue<F>,
) -> AssignedValue<F> {
    let or_ab = gate.or(ctx, a, b);
    let and_ab = gate.and(ctx, a, b);
    let not_and_ab = gate.not(ctx, and_ab);
    gate.and(ctx, or_ab, not_and_ab)
}



pub fn sha256_compression<F: ScalarField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    input_bytes: &[AssignedValue<F>],
    last_hash_words: &[AssignedValue<F>],
) -> Vec<AssignedValue<F>> {
    debug_assert_eq!(input_bytes.len(), 64);
    debug_assert_eq!(last_hash_words.len(), 8);

    let gate = range.gate();

    let mut message_u32s: Vec<AssignedValue<F>> = input_bytes
        .chunks(4)
        .map(|bytes| {
            let mut sum = ctx.load_zero();
            for idx in 0..4 {
                sum = gate.mul_add(
                    ctx,
                    bytes[3 - idx],
                    Constant(F::from(1u64 << (8 * idx))),
                    sum,
                );
            }
            sum
        })
        .collect_vec();

    // Convert words to bits
    let mut message_bits = message_u32s
        .iter()
        .map(|val: &AssignedValue<F>| gate.num_to_bits(ctx, *val, 32))
        .collect_vec();

    // Expansion to 64 words
    for idx in 16..64 {
        let term1_bits = sigma1(ctx, gate, &message_bits[idx - 2]);
        let term3_bits = sigma0(ctx, gate, &message_bits[idx - 15]);

        let term1_u32 = bits2u32(ctx, gate, &term1_bits);
        let term3_u32 = bits2u32(ctx, gate, &term3_bits);

        let new_w = {
            let add1 = gate.add(
                ctx,
                term1_u32,
                message_u32s[idx - 7],
            );
            let add2 = gate.add(
                ctx,
                add1,
                term3_u32,
            );
            let add3 = gate.add(
                ctx,
                add2,
                message_u32s[idx - 16],
            );
            mod_u32(ctx, &range, &add3)
        };
        message_u32s.push(new_w.clone());
        // TODO: underconstrained
        if idx <= 61 {
            let new_w_bits = gate.num_to_bits(ctx, new_w, 32);
            message_bits.push(new_w_bits);
        }
    }

    // Compression
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) = (
        last_hash_words[0].clone(),
        last_hash_words[1].clone(),
        last_hash_words[2].clone(),
        last_hash_words[3].clone(),
        last_hash_words[4].clone(),
        last_hash_words[5].clone(),
        last_hash_words[6].clone(),
        last_hash_words[7].clone(),
    );

    let mut a_bits = gate.num_to_bits(ctx, a, 32);
    let mut b_bits = gate.num_to_bits(ctx, b, 32);
    let mut c_bits = gate.num_to_bits(ctx, c, 32);
    let mut e_bits = gate.num_to_bits(ctx, e, 32);
    let mut f_bits = gate.num_to_bits(ctx, f, 32);
    let mut g_bits = gate.num_to_bits(ctx, g, 32);
    for idx in 0..64 {
        let t1 = {
            let sigma_term = usigma1(ctx, gate, &e_bits);
            let sigma_term = bits2u32(ctx, gate, &sigma_term);
            let ch_term = ch(ctx, gate, &e_bits, &f_bits, &g_bits);
            let ch_term = bits2u32(ctx, gate, &ch_term);
            let add1 = gate.add(
                ctx,
                h,
                sigma_term,
            );
            let add2 = gate.add(
                ctx,
                add1,
                ch_term,
            );
            let add3 = gate.add(
                ctx,
                add2,
                Constant(F::from(ROUND_CONSTANTS[idx] as u64)),
            );
            let add4 = gate.add(
                ctx,
                add3,
                message_u32s[idx],
            );
            mod_u32(ctx, &range, &add4)
        };
        let t2 = {
            let sigma_term = usigma0(ctx, gate, &a_bits);
            let sigma_term = bits2u32(ctx, gate, &sigma_term);
            let maj_term = maj(ctx, gate, &a_bits, &b_bits, &c_bits);
            let maj_term = bits2u32(ctx, gate, &maj_term);
            let add = gate.add(
                ctx,
                sigma_term,
                maj_term,
            );
            mod_u32(ctx, range, &add)
        };
        h = g;
        g = f;
        g_bits = f_bits;
        f = e;
        f_bits = e_bits;
        e = {
            let add = gate.add(ctx, d, t1);
            mod_u32(ctx, range, &add)
        };
        e_bits = gate.num_to_bits(ctx, e, 32);
        d = c;
        c = b;
        c_bits = b_bits;
        b = a;
        b_bits = a_bits;
        a = {
            let add = gate.add(ctx, t1, t2);
            mod_u32(ctx, range, &add)
        };
        a_bits = gate.num_to_bits(ctx, a, 32);
    }
    let new_states = vec![a, b, c, d, e, f, g, h];
    let next_state_words = new_states
        .iter()
        .zip(last_hash_words.iter())
        .map(|(x, y)| {
            let add = gate.add(ctx, *x, *y);
            mod_u32(ctx, range, &add)
        })
        .collect_vec();

    next_state_words
}

pub fn rotr<F: ScalarField>(
    _ctx: &mut Context<F>,
    _gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>],
    n: usize
) -> Vec<AssignedValue<F>> {
    debug_assert_eq!(x_bits.len(), 32);
    // Rotate right by n bits
    // TODO: underconstrained
    (0..32)
        .map(|idx| x_bits[(idx + n) % 32].clone())
        .collect_vec()
}

fn ch<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>],
    y_bits: &[AssignedValue<F>],
    z_bits: &[AssignedValue<F>],
) -> Vec<AssignedValue<F>> {
    debug_assert_eq!(x_bits.len(), 32);
    debug_assert_eq!(y_bits.len(), 32);
    debug_assert_eq!(z_bits.len(), 32);

    // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/ch.circom
    let y_sub_z: Vec<AssignedValue<F>> = y_bits
        .iter()
        .zip(z_bits.iter())
        .map(|(y, z)| gate.sub(ctx, *y, *z))
        .collect_vec();
    x_bits
        .iter()
        .zip(y_sub_z.iter())
        .zip(z_bits.iter())
        .map(|((x, y), z)| {
            gate.mul_add(
                ctx,
                *x,
                *y,
                *z,
            )
        })
        .collect_vec()
}

pub fn shr<F: ScalarField>(
    ctx: &mut Context<F>,
    _gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>],
    n: usize
) -> Vec<AssignedValue<F>> {
    debug_assert_eq!(x_bits.len(), 32);
    // TODO: Underconstrained
    let zero = ctx.load_zero();
    (0..32)
        .map(|idx| {
            // TODO: underconstrained
            if idx + n >= 32 {
                zero.clone()
            } else {
                x_bits[idx + n].clone()
            }
        })
        .collect_vec()
}

fn maj<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>],
    y_bits: &[AssignedValue<F>],
    z_bits: &[AssignedValue<F>],
) -> Vec<AssignedValue<F>> {
    debug_assert_eq!(x_bits.len(), 32);
    debug_assert_eq!(y_bits.len(), 32);
    debug_assert_eq!(z_bits.len(), 32);
    // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/maj.circom
    let mid: Vec<AssignedValue<F>> = y_bits
        .iter()
        .zip(z_bits.iter())
        .map(|(y, z)| gate.mul(ctx, *y, *z))
        .collect_vec();
    (0..32)
        .map(|idx| {
            let add1 = gate.add(
                ctx,
                y_bits[idx],
                z_bits[idx],
            );
            let add2 = gate.mul_add(
                ctx,
                mid[idx],
                Constant(-F::from(2u64)),
                add1,
            );
            gate.mul_add(
                ctx,
                x_bits[idx],
                add2,
                mid[idx],
            )
        })
        .collect_vec()
}

pub fn sigma0<F: ScalarField> (
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>]
) -> Vec<AssignedValue<F>> {

    let rotr_7 = rotr(
        ctx,
        &gate,
        x_bits,
        7
    );

    let rotr_18 = rotr(
        ctx,
        &gate,
        x_bits,
        18
    );

    let shr_3 = shr(
        ctx,
        &gate,
        x_bits,
        3
    );


    let result = rotr_7
        .iter()
        .zip(rotr_18.iter())
        .zip(shr_3.iter())
        .map(|((x, y), z)| {
            let a = xor(
                gate,
                ctx, 
                *x, 
                *y
            );
            xor(
                gate,
                ctx, 
                a, 
                *z
            )
        })
        .collect_vec();
        
    result

}

pub fn sigma1<F: ScalarField> (
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>]
) -> Vec<AssignedValue<F>> {

    let rotr_17 = rotr(
        ctx,
        &gate,
        x_bits,
        17
    );

    let rotr_19 = rotr(
        ctx,
        &gate,
        x_bits,
        19
    );

    let shr_10 = shr(
        ctx,
        &gate,
        x_bits,
        10
    );

    let result = rotr_17
        .iter()
        .zip(rotr_19.iter())
        .zip(shr_10.iter())
        .map(|((x, y), z)| {
            let a = xor(
                gate,
                ctx, 
                *x, 
                *y
            );
            xor(
                gate,
                ctx, 
                a, 
                *z
            )
        })
        .collect_vec();

    result
}


pub fn usigma0<F: ScalarField> (
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>]
) -> Vec<AssignedValue<F>> {

    let rotr_2 = rotr(
        ctx,
        &gate,
        x_bits,
        2
    );

    let rotr_13 = rotr(
        ctx,
        &gate,
        x_bits,
        13
    );

    let rotr_22 = rotr(
        ctx,
        &gate,
        x_bits,
        22
    );

    let result = rotr_2
        .iter()
        .zip(rotr_13.iter())
        .zip(rotr_22.iter())
        .map(|((x, y), z)| {
            let a = xor(
                gate,
                ctx, 
                *x, 
                *y
            );
            xor(
                gate,
                ctx, 
                a, 
                *z
            )
        })
        .collect_vec();

    result
}

pub fn usigma1<F: ScalarField> (
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    x_bits: &[AssignedValue<F>]
) -> Vec<AssignedValue<F>> {

    let rotr_6 = rotr(
        ctx,
        &gate,
        x_bits,
        6
    );

    let rotr_11 = rotr(
        ctx,
        &gate,
        x_bits,
        11
    );

    let rotr_25 = rotr(
        ctx,
        &gate,
        x_bits,
        25
    );

    let result = rotr_6
        .iter()
        .zip(rotr_11.iter())
        .zip(rotr_25.iter())
        .map(|((x, y), z)| {
            let a = xor(
                gate,
                ctx, 
                *x, 
                *y
            );
            xor(
                gate,
                ctx, 
                a, 
                *z
            )
        })
        .collect_vec();

    result
}

fn bits2u32<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    bits: &[AssignedValue<F>]
) -> AssignedValue<F> {
    debug_assert_eq!(bits.len(), 32);
    let mut sum = ctx.load_zero();
    for idx in 0..32 {
        sum = gate.mul_add(
            ctx,
            bits[idx],
            Constant(F::from(1u64 << idx)),
            sum,
        );
    }
    sum
}

fn mod_u32<F: ScalarField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    x: &AssignedValue<F>,
) -> AssignedValue<F> {
    let gate = range.gate();
    let v: &F = x.value();
    let lo = F::from(v.get_lower_32() as u64);
    let hi = F::from(((v.get_lower_64() >> 32) & ((1u64 << 32) - 1)) as u64);
    let assigned_lo = ctx.load_witness(lo);
    let assigned_hi = ctx.load_witness(hi);
    range.range_check(ctx, assigned_lo, 32);
    let composed = gate.mul_add(
        ctx,
        assigned_hi,
        Constant(F::from(1u64 << 32)),
        assigned_lo,
    );
    gate.is_equal(
        ctx,
        *x,
        composed,
    );
    assigned_lo
}

#[cfg(test)]
mod test {
    use std::vec;

    use super::*;
    use halo2_base::utils::testing::base_test;
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_rotr() {
        let k = 9;

        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
        let n = 1;

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            // Load witness
            let mut x_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }
        
            let result = rotr(
                ctx,
                &range.gate(),
                &x_assigned_bits,
                n,
            );
            let result_rev: Vec<&AssignedValue<Fr>> = result.iter().rev().collect_vec();
        
            let expected = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0];
        
            for i in 0..32 {
                assert_eq!(result_rev[i].value(), &Fr::from(expected[i]));
            };
        });

    }
    
    #[test]
    fn test_choose() {
        let k = 9;
    
        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
        let y_bits = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0];
        let z_bits = [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1];
        
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            // Load witness
            let mut x_assigned_bits = vec![];
            let mut y_assigned_bits = vec![];
            let mut z_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
                y_assigned_bits.push(ctx.load_witness(Fr::from(y_bits[i])));
                z_assigned_bits.push(ctx.load_witness(Fr::from(z_bits[i])));
            }

            let result = ch(
                ctx,
                &range.gate(),
                &x_assigned_bits,
                &y_assigned_bits,
                &z_assigned_bits
            );
        
            let expected = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0];
        
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            };
        });
    
    }

    #[test]
    fn test_shr() {
        let k = 9;
    
        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
        let bits = 10;
        
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            // Load witness
            let mut x_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }
        
            let result = shr(
                ctx,
                &range.gate(),
                &x_assigned_bits,
                bits
            );
    
            // Need to reverse order of result
            let expected = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0];
            
            for i in 0..32 {
                assert_eq!(result[31 - i].value(), &Fr::from(expected[i]));
            }
        });
    }

    #[test]
    fn test_maj() {
        let k = 9;
    
        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
        let y_bits = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0];
        let z_bits = [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1];
        
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let mut x_assigned_bits = vec![];
            let mut y_assigned_bits = vec![];
            let mut z_assigned_bits = vec![];

            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
                y_assigned_bits.push(ctx.load_witness(Fr::from(y_bits[i])));
                z_assigned_bits.push(ctx.load_witness(Fr::from(z_bits[i])));
            }

            let result = maj(
                ctx,
                &range.gate(),
                &x_assigned_bits,
                &y_assigned_bits,
                &z_assigned_bits
            );
        
            let expected = [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1];
        
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            }
        });
    }

    #[test]
    fn test_sigma0() {
        let k = 9;

        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let mut x_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }
    
            let result = sigma0(
                ctx, 
                &range.gate(),
                &x_assigned_bits
            );
    
            // println!("result: {:?}", result.iter().map(|x| x.value()).collect_vec());
    
            // TODO: Ensure that the result is correct. For now, we just print the result and set the expected value.
    
            let expected = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0];
    
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            }
        });

    }

    #[test]
    fn test_sigma1() {
        let k = 9;

        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let mut x_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }

            let result = sigma1(
                ctx,
                &range.gate(),
                &x_assigned_bits
            );
    
            // Todo: Ensure that the result is correct. For now, we just print the result and set the expected value.
            // println!("result: {:?}", result.iter().map(|x| x.value()).collect_vec());
            let expected = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            }
        });

    }

    #[test]
    fn test_usigma0() {
        let k = 9;
        
        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
        
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let mut x_assigned_bits = vec![];

            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }

            let result = usigma0(
                ctx,
                &range.gate(),
                &x_assigned_bits
            );
    
            // Note: Ensure that the result is correct. For now, we just print the result and set the expected value.
            // println!("result: {:?}", result.iter().map(|x| x.value()).collect_vec());
            let expected = [0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1];
    
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            }
        });

    }

    #[test]
    fn test_usigma1() {
        let k = 9;

        let x_bits = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let mut x_assigned_bits = vec![];
            for i in 0..32 {
                x_assigned_bits.push(ctx.load_witness(Fr::from(x_bits[i])));
            }
    
            let result = usigma1(
                ctx,
                &range.gate(),
                &x_assigned_bits
            );
    
            // Note: Ensure that the result is correct. For now, we just print the result and set the expected value.
            // println!("result: {:?}", result.iter().map(|x| x.value()).collect_vec());
            let expected = [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1];
    
            for i in 0..32 {
                assert_eq!(result[i].value(), &Fr::from(expected[i]));
            }
        });
    }

    #[test]
    fn test_mod_u32() {
        let k = 9;
        
        let x = 10000000000000000000 as u64;
        
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let x_assigned = ctx.load_witness(Fr::from(x));
            let result = mod_u32(
                ctx,
                &range,
                &x_assigned
            );
    
            // Note: Ensure that the result is correct. For now, we just print the result and set the expected value.
            // expected = 10000000000000000000 % (2**32)
            let expected = 2313682944 as u64;
    
            assert_eq!(result.value(), &Fr::from(expected));
        });
    }

}