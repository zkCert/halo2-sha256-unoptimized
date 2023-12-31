mod utils;
pub use utils::*;
use halo2_base::halo2_proofs::plonk::Error;
use halo2_base::QuantumCell::Constant;
use halo2_base::{
    gates::{GateInstructions, RangeInstructions, RangeChip},
    utils::ScalarField,
    AssignedValue, Context,
};
use generic_array::GenericArray;
use sha2::compress256;
use itertools::Itertools;

#[derive(Debug, Clone)]
pub struct AssignedHashResult<F: ScalarField> {
    pub input_len: AssignedValue<F>,
    pub input_bytes: Vec<AssignedValue<F>>,
    pub output_bytes: Vec<AssignedValue<F>>,
}

#[derive(Debug, Clone)]
pub struct Sha256Chip<F: ScalarField> {
    pub max_byte_sizes: Vec<usize>,
    pub range: RangeChip<F>,
    pub cur_hash_idx: usize,
    pub is_input_range_check: bool,
}

impl<F: ScalarField> Sha256Chip<F> {
    // 64 bytes = 512 bits
    const ONE_ROUND_INPUT_BYTES: usize = 64;
    pub fn construct(
        max_byte_sizes: Vec<usize>,
        range: RangeChip<F>,
        is_input_range_check: bool,
    ) -> Self {
        for byte in max_byte_sizes.iter() {
            debug_assert_eq!(byte % Self::ONE_ROUND_INPUT_BYTES, 0);
        }
        Self {
            max_byte_sizes,
            range,
            cur_hash_idx: 0,
            is_input_range_check
        }
    }

    pub fn digest(
        &mut self,
        ctx: &mut Context<F>,
        input: &[u8],
        precomputed_input_len: Option<usize>,
    ) -> Result<AssignedHashResult<F>, Error> {
        let input_byte_size = input.len();
        let input_byte_size_with_9 = input_byte_size + 9;
        let one_round_size = Self::ONE_ROUND_INPUT_BYTES;
        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        let padded_size = one_round_size * num_round;
        let max_variable_byte_size = self.max_byte_sizes[self.cur_hash_idx];
        let max_variable_round = max_variable_byte_size / one_round_size;
        let precomputed_input_len = precomputed_input_len.unwrap_or(0);
        assert_eq!(precomputed_input_len % one_round_size, 0);
        assert!(padded_size - precomputed_input_len <= max_variable_byte_size);
        let zero_padding_byte_size = padded_size - input_byte_size_with_9;
        let remaining_byte_size = max_variable_byte_size + precomputed_input_len - padded_size;
        let precomputed_round = precomputed_input_len / one_round_size;
        assert_eq!(
            remaining_byte_size,
            one_round_size * (max_variable_round + precomputed_round - num_round)
        );
        let mut padded_inputs = input.to_vec();
        padded_inputs.push(0x80);
        for _ in 0..zero_padding_byte_size {
            padded_inputs.push(0);
        }
        let mut input_len_bytes = [0; 8];
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        for byte in input_len_bytes.iter().rev() {
            padded_inputs.push(*byte);
        }

        assert_eq!(padded_inputs.len(), num_round * one_round_size);
        for _ in 0..remaining_byte_size {
            padded_inputs.push(0);
        }
        assert_eq!(
            padded_inputs.len(),
            max_variable_byte_size + precomputed_input_len
        );
        // for (idx, byte) in padded_inputs.iter().enumerate() {
        //     println!("idx {} byte {}", idx, byte);
        // }

        let range = self.range.clone();
        let gate = range.gate();
        let assigned_input_byte_size =
            ctx.load_witness(F::from(input_byte_size as u64));
        let assigned_num_round = ctx.load_witness(F::from(num_round as u64));
        let assigned_padded_size = gate.mul(
            ctx,
            assigned_num_round,
            Constant(F::from(one_round_size as u64)),
        );
        let assigned_input_with_9_size = gate.add(
            ctx,
            assigned_input_byte_size,
            Constant(F::from(9u64)),
        );
        let padding_size = gate.sub(
            ctx,
            assigned_padded_size,
            assigned_input_with_9_size,
        );
        let padding_is_less_than_round =
            range.is_less_than_safe(ctx, padding_size, one_round_size as u64);
        gate.assert_is_const(ctx, &padding_is_less_than_round, &F::from(1));
        let assigned_precomputed_round =
            ctx.load_witness(F::from(precomputed_round as u64));
        let assigned_target_round = gate.sub(
            ctx,
            assigned_num_round,
            assigned_precomputed_round,
        );

        // compute an initial state from the precomputed_input.
        let precomputed_input = &padded_inputs[0..precomputed_input_len];
        let mut last_state = INIT_HASH_VALUES;
        let precomputed_blocks = precomputed_input
            .chunks(one_round_size)
            .map(|bytes| GenericArray::clone_from_slice(bytes))
            .collect_vec();
        compress256(&mut last_state, &precomputed_blocks[..]);

        let mut assigned_last_state_vec = vec![last_state
            .iter()
            .map(|state| ctx.load_witness(F::from(*state as u64)))
            .collect_vec()];
        // vec![INIT_HASH_VALUES
        //     .iter()
        //     .map(|h| gate.load_constant(ctx, F::from(*h as u64)))
        //     .collect::<Vec<AssignedValue<F>>>()];
        let assigned_input_bytes = padded_inputs[precomputed_input_len..]
            .iter()
            .map(|byte| ctx.load_witness(F::from(*byte as u64)))
            .collect::<Vec<AssignedValue<F>>>();
        if self.is_input_range_check {
            for assigned_byte in assigned_input_bytes.iter() {
                range.range_check(ctx, *assigned_byte, 8);
            }
        }
        let mut num_processed_input = 0;
        while num_processed_input < max_variable_byte_size {
            let assigned_input_word_at_round =
                &assigned_input_bytes[num_processed_input..(num_processed_input + one_round_size)];
            let new_assigned_hs_out = sha256_compression(
                ctx,
                &range,
                assigned_input_word_at_round,
                &assigned_last_state_vec.last().unwrap(),
            );

            assigned_last_state_vec.push(new_assigned_hs_out);
            num_processed_input += one_round_size;
        }

        let zero = ctx.load_zero();
        let mut output_h_out = vec![zero; 8];
        for (n_round, assigned_state) in assigned_last_state_vec.into_iter().enumerate() {
            let selector = gate.is_equal(
                ctx,
                Constant(F::from(n_round as u64)),
                assigned_target_round,
            );
            for i in 0..8 {
                output_h_out[i] = gate.select(
                    ctx,
                    assigned_state[i],
                    output_h_out[i],
                    selector,
                )
            }
        }
        let output_digest_bytes = output_h_out
            .into_iter()
            .flat_map(|assigned_word| {
                let be_bytes = assigned_word
                    .value()
                    .get_lower_32().to_be_bytes().to_vec();
                let assigned_bytes = (0..4)
                    .map(|idx| {
                        let assigned = ctx.load_witness(F::from(be_bytes[idx] as u64));
                        range.range_check(ctx, assigned, 8);
                        assigned
                    })
                    .collect::<Vec<AssignedValue<F>>>();
                let mut sum = ctx.load_zero();
                for (idx, assigned_byte) in assigned_bytes.iter().enumerate() {
                    sum = gate.mul_add(
                        ctx,
                        *assigned_byte,
                        Constant(F::from(1u64 << (24 - 8 * idx))),
                        sum,
                    );
                }
                ctx.constrain_equal(
                    &assigned_word,
                    &sum,
                );
                assigned_bytes
            })
            .collect::<Vec<AssignedValue<F>>>();
        let result = AssignedHashResult {
            input_len: assigned_input_byte_size,
            input_bytes: assigned_input_bytes,
            output_bytes: output_digest_bytes,
        };
        self.cur_hash_idx += 1;
        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use std::vec;

    use super::*;
    use halo2_base::utils::testing::base_test;
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
    use hex;
    use rand::{thread_rng, Rng};
    use sha2::{Digest, Sha256};

    #[test]
    fn test_sha256_1() {
        let k = 17;

        // Test vector: "abc"
        let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

        let test_output: [u8; 32] = [
            0b10111010, 0b01111000, 0b00010110, 0b10111111, 0b10001111, 0b00000001, 0b11001111,
            0b11101010, 0b01000001, 0b01000001, 0b01000000, 0b11011110, 0b01011101, 0b10101110,
            0b00100010, 0b00100011, 0b10110000, 0b00000011, 0b01100001, 0b10100011, 0b10010110,
            0b00010111, 0b01111010, 0b10011100, 0b10110100, 0b00010000, 0b11111111, 0b01100001,
            0b11110010, 0b00000000, 0b00010101, 0b10101101,
        ];
        let max_byte_sizes = vec![64];
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let range = range.clone();
            let mut chip = Sha256Chip::construct(max_byte_sizes, range, true);

            let outputs = chip.digest(ctx, &test_input, Some(0)).unwrap();
            assert_eq!(&Fr::from(test_input.len() as u64), outputs.input_len.value());
            for i in 0..32 {
                assert_eq!(&Fr::from(test_output[i] as u64), outputs.output_bytes[i].value());
            }
        });

    }

    #[test]
    fn test_sha256_2() {
        let k = 17;

        // Test vector: "0x0"
        let test_input = vec![0u8];

        let test_output =
            hex::decode("6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d")
                .unwrap();
        let max_byte_sizes = vec![64];
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let range = range.clone();
            let mut chip = Sha256Chip::construct(max_byte_sizes, range, true);

            let outputs = chip.digest(ctx, &test_input, Some(0)).unwrap();
            assert_eq!(&Fr::from(test_input.len() as u64), outputs.input_len.value());
            for i in 0..32 {
                assert_eq!(&Fr::from(test_output[i] as u64), outputs.output_bytes[i].value());
            }
        });

    }

    #[test]
    fn test_sha256_3() {
        let k = 17;

        // Test vector: "0x0"
        let test_input = vec![0x1; 56];

        let test_output =
            hex::decode("51e14a913680f24c85fe3b0e2e5b57f7202f117bb214f8ffdd4ea0f4e921fd52")
                .unwrap();
        let max_byte_sizes = vec![128];
        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let range = range.clone();
            let mut chip = Sha256Chip::construct(max_byte_sizes, range, true);

            let outputs = chip.digest(ctx, &test_input, Some(0)).unwrap();
            assert_eq!(&Fr::from(test_input.len() as u64), outputs.input_len.value());
            for i in 0..32 {
                assert_eq!(&Fr::from(test_output[i] as u64), outputs.output_bytes[i].value());
            }
        });
    }
    
    #[test]
    fn test_sha256_4() {
        let k = 17;

        fn gen_random_bytes(len: usize) -> Vec<u8> {
            let mut rng = thread_rng();
            (0..len).map(|_| rng.gen::<u8>()).collect()
        }

        let test_input = gen_random_bytes(128 + 64);

        let test_output = Sha256::digest(&test_input);

        // Ensure sufficient size including padding
        let max_byte_sizes = vec![256];

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            let range = range.clone();
            let mut chip = Sha256Chip::construct(max_byte_sizes, range, true);

            let outputs = chip.digest(ctx, &test_input, Some(0)).unwrap();
            assert_eq!(&Fr::from(test_input.len() as u64), outputs.input_len.value());
            for i in 0..32 {
                assert_eq!(&Fr::from(test_output[i] as u64), outputs.output_bytes[i].value());
            }
        });
    }
}
