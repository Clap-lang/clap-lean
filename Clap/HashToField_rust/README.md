# HashToField reference-vector generator

`hash_to_field.rs` is a copy of
[`keyless-zk-proofs/circuit/src/hash_to_field.rs`](https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/src/hash_to_field.rs)
with one addition: the `print_hashtofield_vectors` test. It prints reference input/output
vectors used by the `native_decide` tests in [`../HashToField.lean`](../HashToField.lean).

## Mapping to the Lean side

- bytes: `pad_and_hash_bytes_with_len(msg, capacity)` ↔
  `hashBytesToField ⟨data, len⟩` with `numBytes = capacity`, `data = msg` zero-padded to
  `capacity`, `len = msg.len()`.
- limbs: `pad_and_hash_limbs_with_len(limbs, capacity)` ↔
  `hash64BitLimbsToField ⟨data, len⟩` with `numLimbs = capacity`, `data = limbs` zero-padded
  to `capacity`, `len = limbs.len()` (the number of limbs).

## Regenerating the vectors

Copy this file over the upstream one in a local checkout of `keyless-zk-proofs`, then run the
test:

```sh
cp hash_to_field.rs <keyless-zk-proofs>/circuit/src/hash_to_field.rs
cd <keyless-zk-proofs>
cargo test -p aptos-keyless-circuit print_hashtofield_vectors -- --nocapture
```

The first build clones and compiles the `aptos-crypto` git dependency. Each line of output
(`BYTES …` / `LIMBS …`) lists `msg`/`limbs`, `len`, `capacity`, and `output`; paste each
`output` decimal into the matching test in `../HashToField.lean`.
