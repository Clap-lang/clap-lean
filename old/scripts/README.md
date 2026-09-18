# Keyless test-fixture generation

Two Python scripts in this folder produce the test fixture used by the
end-to-end Lean tests of the Aptos Keyless circuit
([Clap/Keyless.lean](../Clap/Keyless.lean)):

```
                            +----------------------+
   prover_handler.rs        |  gen_input.py        |
   scenario specs           |  (signed JWT +       |     input.json
   (default, with_email)    |  field indices +     | ──────────────►
   ───────────────────────► |  RSA limbs +         |
                            |  SHA padding)        |
                            +----------------------+
                                                          │
                                                          ▼
                            +----------------------+   Clap/Test/
                            |  input_json_to_      |   KeylessFixture.lean
                            |  lean.py             | ─────────────────►
   scenario kind:Namespace  |  (Array Nat,         |   (KeylessTestFixture.
   pairs                    |  Vector (F bn254),   |    Happy / AudOverride /
   ───────────────────────► |  FString bn254,      |    SkipAudChecks /
                            |  KeylessInput)       |    WithEmail)
                            +----------------------+
                                                          │
                                                          ▼
                                                Clap/Test/Keyless.lean
                                                end-to-end tests
                                                (`example : keyless x = some ()`)
```

## Prerequisites
`
```bash
python3 -m venv /tmp/keyless-venv
/tmp/keyless-venv/bin/pip install pyjwt pycryptodome cryptography
```

`gen_input.py` also needs the canonical RSA test private key, which lives
in the upstream submodule at
`keyless-zk-proofs/circuit/tools/test_rsa_privkey.pem`. The path must
be passed explicitly via `--privkey` (the script intentionally has no
default so the upstream key location is never silently assumed).

## `gen_input.py` — generate `input.json`

Produces the CIRCOM-format witness that the upstream `input_gen.py`
emits, but parameterized by *scenario* so we can cover JWT shapes beyond
the single hardcoded one upstream supports.

The file is a **near-verbatim copy** of upstream `keyless-zk-proofs/circuit/tools/input_gen.py`
with one localized `CLAP-CONFIG` block at the top and a handful of
`# CLAP: …`-marked in-body changes. Audit with:

```bash
diff -u keyless-zk-proofs/circuit/tools/input_gen.py scripts/gen_input.py
```

### Usage

```bash
/tmp/keyless-venv/bin/python scripts/gen_input.py \
    --scenario {default|with_email} \
    --privkey PATH                     # required; canonical key at keyless-zk-proofs/circuit/tools/test_rsa_privkey.pem
    [--out PATH]                       # default: ./input.json
```

### Scenarios

| `--scenario`   | Mirrors Rust test `prove_request_…`     | JWT shape                        | `uid_key` | `extra_field` |
|----------------|------------------------------------------|----------------------------------|-----------|---------------|
| `default`      | `_default_request` / `_with_sub` / `_with_no_extra_field` / `_with_sub_no_email_verified` | upstream's hardcoded Michael-Straka JWT | `sub`     | `family_name` (placeholder; gated off by `use_extra_field=0`) |
| `with_email`   | `_with_email`                            | Google JWT including `email` and `email_verified` fields | `email`   | none          |

The `default` scenario produces output **byte-identical** to upstream's
checked-in `circuit/input.json`.

### Pinned cryptographic values

Every scenario must respect these constants because they are baked into
the test ephemeral-key triple `(temp_pubkey_*, jwt_randomness)` in both
this script and `Clap/Test/KeylessFixtureHelpers.lean`:

* `iat   = 1719866138`
* `nonce = "2284473333442251804379681643965308154311773667525398119496797545594705356495"`
  (= `Poseidon([temp_pubkey_*, temp_pubkey_len, exp_date, jwt_randomness])`)

Adding a scenario with a different ephemeral key requires recomputing the
nonce and updating `KeylessTestFixture` to match.

## `input_json_to_lean.py` — convert `input.json` to a Lean fixture

Reads one or more `input.json` files (the malformed-JSON shape upstream
emits is tolerated by a comma-insertion regex) and writes a Lean module
that imports `Clap.Test.KeylessFixtureHelpers` and defines one
`namespace <Name>` per scenario inside the outer `KeylessTestFixture`
namespace.

Each namespace exposes:

* a fully-typed `KeylessInput` named `base` (with `publicInputsHash := 0` placeholder), and
* a `def input := { base with publicInputsHash := … }` whose hash is
  re-derived in Lean via
  `KeylessTestFixture.computePublicInputsHash` — this is intentional
  because upstream's hardcoded `public_inputs_hash` has been observed to
  drift out of sync with the rest of the witness.

### Usage

```bash
/tmp/keyless-venv/bin/python scripts/input_json_to_lean.py \
    --input PATH/input.json \
    --scenario kind:Namespace [--scenario kind:Namespace …] \
    [--out PATH]                       # default: stdout
    [--no-preamble]                    # omit imports + outer namespace
```

`kind` is one of:

* `happy` — verbatim, no mutation (the canonical scenario for the supplied input.json).
* `aud_override` — flips `use_aud_override=1` and copies the JWT-aud into `override_aud_value` so the Quoted-field parser still accepts the JWT. Models `prove_request_with_aud_recovery`.
* `skip_aud_checks` — flips `skip_aud_checks=1`, leaving every other input intact. Exercises the IDC-migration / aud-bypass path.

`Namespace` is the Lean namespace name to emit inside `KeylessTestFixture`
(e.g. `Happy`, `AudOverride`).

## End-to-end workflow

To regenerate `Clap/Test/KeylessFixture.lean` from scratch:

```bash
# 1. Use the upstream input.json as the base for Happy/AudOverride/SkipAudChecks.
#    (Generated once by upstream's `input_gen.py`; checked in.)
UPSTREAM=keyless-zk-proofs/circuit/input.json
PRIVKEY=keyless-zk-proofs/circuit/tools/test_rsa_privkey.pem

# 2. Generate the WithEmail input.json (uid_key=email).
/tmp/keyless-venv/bin/python scripts/gen_input.py \
    --scenario with_email --privkey "$PRIVKEY" --out /tmp/with_email.json

# 3. Convert upstream's input.json into 3 namespaces.
/tmp/keyless-venv/bin/python scripts/input_json_to_lean.py \
    --input "$UPSTREAM" \
    --scenario happy:Happy \
    --scenario aud_override:AudOverride \
    --scenario skip_aud_checks:SkipAudChecks \
    --out Clap/Test/KeylessFixture.lean

# 4. Append the WithEmail namespace from /tmp/with_email.json.
/tmp/keyless-venv/bin/python scripts/input_json_to_lean.py \
    --input /tmp/with_email.json \
    --scenario happy:WithEmail \
    --no-preamble \
    --out /tmp/with_email_ns.lean
python3 -c "
fixture = 'Clap/Test/KeylessFixture.lean'
text = open(fixture).read()
ns   = open('/tmp/with_email_ns.lean').read()
open(fixture, 'w').write(text.replace('end KeylessTestFixture', ns + '\nend KeylessTestFixture', 1))
"

# 5. Build everything (~12 min — runs SHA-256 + RSA-2048 + Poseidon for
#    every end-to-end test).
lake build Clap.Test.Keyless
```

## Adding a new scenario

If the new scenario reuses the upstream JWT (only twiddles flags like
`use_aud_override`, `skip_aud_checks`, or `use_extra_field`):

1. Add a transformation to `SCENARIOS` in `input_json_to_lean.py` (see
   the existing `scenario_aud_override` / `scenario_skip_aud_checks`).
2. Pass it through with a fresh `--scenario kind:Namespace` invocation.

If the new scenario needs a different JWT shape (different `aud`, `sub`,
`email`, etc.):

1. Add a scenario entry to `CLAP_SCENARIOS` in `gen_input.py` with the
   required `jwt_dict`, `uid_key`, and `extra_field_name`. Keep the
   pinned `iat`/`nonce` values from `CLAP_GOOGLE_JWT` unless you also
   plan to regenerate the ephemeral-key triple.
2. Run `gen_input.py --scenario newname` to produce a fresh
   `input.json`.
3. Pass that input to `input_json_to_lean.py`
   (`--scenario happy:NewName`) and splice the namespace into
   `Clap/Test/KeylessFixture.lean`.
4. Add the corresponding `example : keyless NewName.input = some ()`
   test in `Clap/Test/Keyless.lean`.
