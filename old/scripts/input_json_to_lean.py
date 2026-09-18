#!/usr/bin/env python3
"""
Convert a CIRCOM `input.json` (as produced by
doc/keyless-zk-proofs/circuit/tools/input_gen.py) into a Lean fixture file
consumed by `Clap/Test/Keyless.lean`.

Usage:
    python3 scripts/input_json_to_lean.py \\
        --input doc/keyless-zk-proofs/circuit/input.json \\
        --scenario happy:Happy \\
        --scenario aud_override:AudOverride \\
        --scenario skip_aud_checks:SkipAudChecks \\
        --out Clap/Test/KeylessFixture.lean

Each `--scenario kind:Namespace` pair produces one Lean namespace inside the
outer `KeylessTestFixture`. Available scenarios:

* ``happy`` — verbatim from `input.json`, modulo the stale
  ``public_inputs_hash`` (always recomputed via the Lean-side helper
  ``KeylessTestFixture.computePublicInputsHash`` since `input_gen.py`'s
  hardcoded value has been observed to drift).
* ``aud_override`` — flips ``use_aud_override`` to 1 and copies the JWT-aud
  value into ``override_aud_value`` so the Quoted-field parser still accepts
  the JWT. Models the Rust `prove_request_with_aud_recovery` test.
* ``skip_aud_checks`` — flips ``skip_aud_checks`` to 1, leaving all aud
  inputs intact; exercises the bypass path where the circuit ignores the
  JWT-aud entirely (used for IDC migration).

The ``public_inputs_hash`` in the fixture is always (re-)derived in Lean —
the JSON's value is ignored.

The fixture file imports `Clap.Test.KeylessFixtureHelpers`, which holds the
hand-written ``mkChar``, ``mkFB`` and ``computePublicInputsHash`` helpers.
"""
from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from pathlib import Path
from typing import Any, Callable


# ---------------------------------------------------------------------------
# Parsing input.json
# ---------------------------------------------------------------------------

def load_input_json(path: Path) -> dict[str, Any]:
    raw = path.read_text()
    fixed = re.sub(r'(\]|")(\s*"[\w_]+"\s*:)', r'\1,\2', raw)
    return json.loads(fixed)


def as_int(s: str | int) -> int:
    if isinstance(s, int):
        return s
    return int(s)


def as_int_list(arr: list[str | int]) -> list[int]:
    return [as_int(x) for x in arr]


# ---------------------------------------------------------------------------
# Scenario mutations
# ---------------------------------------------------------------------------

def scenario_happy(_j: dict[str, Any]) -> None:
    """No-op: keep input.json as-is."""
    return


def scenario_aud_override(j: dict[str, Any]) -> None:
    """Flip use_aud_override=1 and copy the JWT aud into override_aud_value.

    With use_aud_override=1, the muxed aud value used by the circuit equals
    `override_aud_value`, which the Quoted-field parser then asserts against
    the JWT. So `override_aud_value` must equal the JWT's actual aud — we
    copy from `private_aud_value` (which holds the JWT aud bytes).
    """
    j["use_aud_override"] = "1"
    j["override_aud_value"] = list(j["private_aud_value"])
    j["override_aud_value_len"] = j["private_aud_value_len"]


def scenario_skip_aud_checks(j: dict[str, Any]) -> None:
    """Flip skip_aud_checks=1 (use_aud_override stays 0).

    With skip_aud_checks=1, `verifyAudField` bypasses every aud-related
    constraint. The IDC computation also drops the `private_aud_value`
    contribution (because `performAudChecks=0` zeros it out).
    """
    j["skip_aud_checks"] = "1"


SCENARIOS: dict[str, Callable[[dict[str, Any]], None]] = {
    "happy":            scenario_happy,
    "aud_override":     scenario_aud_override,
    "skip_aud_checks":  scenario_skip_aud_checks,
}


# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------

def emit_nat_array(name: str, vals: list[int], indent: str = "") -> str:
    body = ", ".join(str(v) for v in vals)
    return f"{indent}private def {name} : Array Nat := #[{body}]"


def emit_field_vector(name: str, vals: list[int], length: int, indent: str = "") -> str:
    body = ", ".join(str(v) for v in vals)
    return (
        f"{indent}def {name} : Vector (F bn254) {length} :=\n"
        f"{indent}  ⟨(#[{body}] : Array Nat).map mkFB,\n"
        f"{indent}   (Array.size_map ..).trans (by native_decide)⟩"
    )


def emit_fb_vector(name: str, vals: list[int], length: int, indent: str = "") -> str:
    body = ", ".join(str(v) for v in vals)
    return (
        f"{indent}def {name} : Vector (FB bn254) {length} :=\n"
        f"{indent}  ⟨(#[{body}] : Array Nat).map mkFB,\n"
        f"{indent}   (Array.size_map ..).trans (by native_decide)⟩"
    )


def emit_fstring(
    var_name: str,
    bytes_array_name: str,
    actual_len: int,
    max_len: int,
    indent: str = "",
) -> str:
    return (
        f"{indent}def {var_name} : FString bn254 {max_len} :=\n"
        f"{indent}  ⟨⟨{bytes_array_name}.map mkChar,\n"
        f"{indent}    (Array.size_map ..).trans (by native_decide)⟩, {actual_len}⟩"
    )


# ---------------------------------------------------------------------------
# Field lengths (mirror Clap/Keyless.lean MAX_*_LEN constants)
# ---------------------------------------------------------------------------

MAX = {
    "jwt_no_sig": 1536,
    "header_w_dot": 300,
    "payload": 1472,
    "aud_pair": 140,
    "aud_name": 40,
    "aud_value": 120,
    "iss_pair": 140,
    "iss_name": 40,
    "iss_value": 120,
    "iat_pair": 50,
    "iat_name": 10,
    "iat_value": 45,
    "nonce_pair": 105,
    "nonce_name": 10,
    "nonce_value": 100,
    "ev_pair": 30,
    "ev_name": 20,
    "ev_value": 10,
    "uid_pair": 350,
    "uid_name": 30,
    "uid_value": 330,
    "extra_pair": 350,
    "rsa_limbs": 32,
    "epk": 3,
}

NAME_LEN = {
    "aud": 3,
    "iss": 3,
    "iat": 3,
    "nonce": 5,
    "ev": 14,
}


# ---------------------------------------------------------------------------
# Per-scenario namespace emission
# ---------------------------------------------------------------------------

def emit(ns_name: str, j: dict[str, Any]) -> str:
    out: list[str] = []
    out.append(f"namespace {ns_name}")
    out.append("")

    payload_unsigned_len = as_int(j["b64_payload_len"])
    header_len = as_int(j["header_len_with_separator"])
    fstring_specs = [
        ("jwtNoSigBytes", "b64uJwtNoSigSha2Padded", "jwt",
         header_len + payload_unsigned_len, MAX["jwt_no_sig"]),
        ("headerBytes", "b64uJwtHeaderWDot", "jwt_header_with_separator",
         header_len, MAX["header_w_dot"]),
        ("payloadShaPaddedBytes", "b64uJwtPayloadSha2Padded", "jwt_payload",
         payload_unsigned_len, MAX["payload"]),
        ("payloadBytes", "b64uJwtPayload", "jwt_payload_without_sha_padding",
         payload_unsigned_len, MAX["payload"]),
        ("audFieldBytes", "audField", "aud_field",
         as_int(j["aud_field_len"]), MAX["aud_pair"]),
        ("audNameBytes", "audName", "aud_name",
         NAME_LEN["aud"], MAX["aud_name"]),
        ("audValueBytes", "audValue", "private_aud_value",
         as_int(j["private_aud_value_len"]), MAX["aud_value"]),
        ("privateAudValueBytes", "privateAudValue", "private_aud_value",
         as_int(j["private_aud_value_len"]), MAX["aud_value"]),
        ("overrideAudValueBytes", "overrideAudValue", "override_aud_value",
         as_int(j["override_aud_value_len"]), MAX["aud_value"]),
        ("uidFieldBytes", "uidField", "uid_field",
         as_int(j["uid_field_len"]), MAX["uid_pair"]),
        ("uidNameBytes", "uidName", "uid_name",
         as_int(j["uid_name_len"]), MAX["uid_name"]),
        ("uidValueBytes", "uidValue", "uid_value",
         as_int(j["uid_value_len"]), MAX["uid_value"]),
        ("issFieldBytes", "issField", "iss_field",
         as_int(j["iss_field_len"]), MAX["iss_pair"]),
        ("issNameBytes", "issName", "iss_name",
         NAME_LEN["iss"], MAX["iss_name"]),
        ("issValueBytes", "issValue", "iss_value",
         as_int(j["iss_value_len"]), MAX["iss_value"]),
        ("iatFieldBytes", "iatField", "iat_field",
         as_int(j["iat_field_len"]), MAX["iat_pair"]),
        ("iatNameBytes", "iatName", "iat_name",
         NAME_LEN["iat"], MAX["iat_name"]),
        ("iatValueBytes", "iatValue", "iat_value",
         as_int(j["iat_value_len"]), MAX["iat_value"]),
        ("nonceFieldBytes", "nonceField", "nonce_field",
         as_int(j["nonce_field_len"]), MAX["nonce_pair"]),
        ("nonceNameBytes", "nonceName", "nonce_name",
         NAME_LEN["nonce"], MAX["nonce_name"]),
        ("nonceValueBytes", "nonceValue", "nonce_value",
         as_int(j["nonce_value_len"]), MAX["nonce_value"]),
        ("evFieldBytes", "evField", "ev_field",
         as_int(j["ev_field_len"]), MAX["ev_pair"]),
        ("evNameBytes", "evName", "ev_name",
         NAME_LEN["ev"], MAX["ev_name"]),
        ("evValueBytes", "evValue", "ev_value",
         as_int(j["ev_value_len"]), MAX["ev_value"]),
        ("extraFieldBytes", "extraField", "extra_field",
         as_int(j["extra_field_len"]), MAX["extra_pair"]),
    ]

    out.append("-- Raw ASCII byte arrays for each FString")
    for (bvar, _, jk, _, max_len) in fstring_specs:
        bytes_ = as_int_list(j[jk])
        if len(bytes_) != max_len:
            raise ValueError(f"{ns_name}: key {jk!r}: expected {max_len} bytes, got {len(bytes_)}")
        out.append(emit_nat_array(bvar, bytes_))
    out.append("")

    out.append("-- FStrings built from the byte arrays above")
    for (bvar, fvar, _, actual_len, max_len) in fstring_specs:
        out.append(emit_fstring(fvar, bvar, actual_len, max_len))
    out.append("")

    out.append("-- String-bodies bit vectors (1 = inside a JSON string body)")
    out.append(emit_fb_vector(
        "audFieldStringBodies", as_int_list(j["aud_field_string_bodies"]),
        MAX["aud_pair"]))
    out.append(emit_fb_vector(
        "uidFieldStringBodies", as_int_list(j["uid_field_string_bodies"]),
        MAX["uid_pair"]))
    out.append(emit_fb_vector(
        "issFieldStringBodies", as_int_list(j["iss_field_string_bodies"]),
        MAX["iss_pair"]))
    out.append(emit_fb_vector(
        "nonceFieldStringBodies", as_int_list(j["nonce_field_string_bodies"]),
        MAX["nonce_pair"]))
    out.append("")

    out.append("-- RSA-2048 signature and modulus, as 32 × 64-bit LSB-first limbs")
    out.append(emit_field_vector(
        "rsaSignature", as_int_list(j["signature"]), MAX["rsa_limbs"]))
    out.append(emit_field_vector(
        "rsaPubkeyModulus", as_int_list(j["pubkey_modulus"]), MAX["rsa_limbs"]))
    out.append("")

    out.append("-- SHA-256 padding signals")
    out.append(emit_field_vector(
        "sha2NumBits", as_int_list(j["jwt_len_bit_encoded"]), 8))
    out.append(emit_field_vector(
        "sha2Padding", as_int_list(j["padding_without_len"]), 64))
    out.append("")

    out.append("-- Ephemeral public key fields")
    out.append(emit_field_vector("epk", as_int_list(j["temp_pubkey"]), MAX["epk"]))
    out.append("")

    scalars = {
        "audIndex":           j["aud_index"],
        "audColonIndex":      j["aud_colon_index"],
        "audValueIndex":      j["aud_value_index"],
        "useAudOverride":     j["use_aud_override"],
        "skipAudChecks":      j["skip_aud_checks"],
        "uidIndex":           j["uid_index"],
        "uidColonIndex":      j["uid_colon_index"],
        "uidValueIndex":      j["uid_value_index"],
        "issIndex":           j["iss_index"],
        "issColonIndex":      j["iss_colon_index"],
        "issValueIndex":      j["iss_value_index"],
        "iatIndex":           j["iat_index"],
        "iatColonIndex":      j["iat_colon_index"],
        "iatValueIndex":      j["iat_value_index"],
        "nonceIndex":         j["nonce_index"],
        "nonceColonIndex":    j["nonce_colon_index"],
        "nonceValueIndex":    j["nonce_value_index"],
        "evIndex":            j["ev_index"],
        "evColonIndex":       j["ev_colon_index"],
        "evValueIndex":       j["ev_value_index"],
        "extraIndex":         j["extra_index"],
        "useExtraField":      j["use_extra_field"],
        "epkLen":             j["temp_pubkey_len"],
        "epkBlinder":         j["jwt_randomness"],
        "expDate":            j["exp_date"],
        "expHorizon":         j["exp_delta"],
        "pepper":             j["pepper"],
        "sha2NumBlocks":      j["jwt_num_sha2_blocks"],
    }
    out.append("-- Scalar field-element signals (publicInputsHash is recomputed; see `input` below)")
    for k, v in scalars.items():
        out.append(f"def {k} : F bn254 := {as_int(v)}")
    out.append("")

    # ---- Bundled KeylessInput: emit `base` (placeholder hash) and `input` (corrected hash) ----
    out.append("/-- The fixture as a single `KeylessInput`, with a placeholder")
    out.append("    `publicInputsHash`. Use `input` (below) for tests — it patches in the")
    out.append("    correctly recomputed hash. -/")
    out.append("def base : KeylessInput := {")
    out.append("  jwtRaw := {")
    out.append("    b64u_jwt_no_sig_sha2_padded  := b64uJwtNoSigSha2Padded")
    out.append("    b64u_jwt_header_w_dot        := b64uJwtHeaderWDot")
    out.append("    b64u_jwt_payload_sha2_padded := b64uJwtPayloadSha2Padded")
    out.append("    b64u_jwt_payload             := b64uJwtPayload")
    out.append("    sha2_num_blocks              := sha2NumBlocks")
    out.append("    sha2_num_bits                := sha2NumBits")
    out.append("    sha2_padding                 := sha2Padding")
    out.append("  }")
    out.append("  rsa := { signature := rsaSignature, pubkeyModulus := rsaPubkeyModulus }")
    out.append("  aud := {")
    out.append("    field             := audField")
    out.append("    name              := audName")
    out.append("    value             := audValue")
    out.append("    fieldStringBodies := audFieldStringBodies")
    out.append("    nameIndex         := audIndex")
    out.append("    colonIndex        := audColonIndex")
    out.append("    valueIndex        := audValueIndex")
    out.append("  }")
    out.append("  audOverride := {")
    out.append("    useAudOverride   := useAudOverride")
    out.append("    skipAudChecks    := skipAudChecks")
    out.append("    privateAudValue  := privateAudValue")
    out.append("    overrideAudValue := overrideAudValue")
    out.append("  }")
    out.append("  uid := {")
    out.append("    field             := uidField")
    out.append("    name              := uidName")
    out.append("    value             := uidValue")
    out.append("    fieldStringBodies := uidFieldStringBodies")
    out.append("    nameIndex         := uidIndex")
    out.append("    colonIndex        := uidColonIndex")
    out.append("    valueIndex        := uidValueIndex")
    out.append("  }")
    out.append("  iss := {")
    out.append("    field             := issField")
    out.append("    name              := issName")
    out.append("    value             := issValue")
    out.append("    fieldStringBodies := issFieldStringBodies")
    out.append("    nameIndex         := issIndex")
    out.append("    colonIndex        := issColonIndex")
    out.append("    valueIndex        := issValueIndex")
    out.append("  }")
    out.append("  iat := {")
    out.append("    field      := iatField")
    out.append("    name       := iatName")
    out.append("    value      := iatValue")
    out.append("    nameIndex  := iatIndex")
    out.append("    colonIndex := iatColonIndex")
    out.append("    valueIndex := iatValueIndex")
    out.append("  }")
    out.append("  nonce := {")
    out.append("    field             := nonceField")
    out.append("    name              := nonceName")
    out.append("    value             := nonceValue")
    out.append("    fieldStringBodies := nonceFieldStringBodies")
    out.append("    nameIndex         := nonceIndex")
    out.append("    colonIndex        := nonceColonIndex")
    out.append("    valueIndex        := nonceValueIndex")
    out.append("  }")
    out.append("  ev := {")
    out.append("    field      := evField")
    out.append("    name       := evName")
    out.append("    value      := evValue")
    out.append("    nameIndex  := evIndex")
    out.append("    colonIndex := evColonIndex")
    out.append("    valueIndex := evValueIndex")
    out.append("  }")
    out.append("  extra := {")
    out.append("    extraField      := extraField")
    out.append("    extraFieldIndex := extraIndex")
    out.append("    useExtraField   := useExtraField")
    out.append("  }")
    out.append("  commit := {")
    out.append("    epk        := epk")
    out.append("    epkLen     := epkLen")
    out.append("    epkBlinder := epkBlinder")
    out.append("    expDate    := expDate")
    out.append("    expHorizon := expHorizon")
    out.append("    pepper     := pepper")
    out.append("  }")
    out.append("  publicInputsHash := 0")
    out.append("}")
    out.append("")
    out.append("/-- The recomputed `publicInputsHash` for `base`, derived from")
    out.append("    `KeylessTestFixture.computePublicInputsHash` (which mirrors the")
    out.append("    Poseidon-14 formula in `verifyPublicInputsHash`). -/")
    out.append("def publicInputsHash : F bn254 := (computePublicInputsHash base).getD 0")
    out.append("")
    out.append("/-- The `KeylessInput` to feed into `keyless` for this scenario. -/")
    out.append("def input : KeylessInput := { base with publicInputsHash := publicInputsHash }")
    out.append("")
    out.append(f"end {ns_name}")

    return "\n".join(out)


# ---------------------------------------------------------------------------
# File-level preamble / postamble
# ---------------------------------------------------------------------------

PREAMBLE = """\
import Clap.Test.KeylessFixtureHelpers

/-!
# Test fixtures for the top-level `Keyless.keyless` circuit

This file is GENERATED by `scripts/input_json_to_lean.py` from the canonical
`input.json` produced by `doc/keyless-zk-proofs/circuit/tools/input_gen.py`.
Each `namespace` below corresponds to one Rust prover-service test scenario
under `doc/keyless-zk-proofs/prover-service/src/tests/prover_handler.rs`.
Do not hand-edit; rerun the script instead.
-/

-- The 1536-byte JWT array literal exceeds Lean's default recursion depth (512).
set_option maxRecDepth 8192

namespace KeylessTestFixture

-- `open ZMod` brings the scoped `instCoreZMod` instance into scope so that
-- `Core bn254` resolves concretely (F := ZMod bn254). We deliberately do
-- *not* declare `variable [Core bn254]`: a free `Core` hypothesis prevents
-- `native_decide` / `decide` from closing Vector size goals.
open Clap.Lang Core Primes ZMod Keyless
"""

POSTAMBLE = """\
end KeylessTestFixture
"""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--input", type=Path, required=True,
        help="Path to canonical input.json (produced by circuit/tools/input_gen.py)",
    )
    p.add_argument(
        "--scenario", action="append", required=True, metavar="kind:Namespace",
        help=f"Scenario to emit, repeatable. kind ∈ {{{', '.join(SCENARIOS)}}}; "
             f"Namespace is the Lean namespace name (e.g. Happy, AudOverride).",
    )
    p.add_argument("--out", type=Path, default=None, help="Output file path; default stdout")
    p.add_argument("--no-preamble", action="store_true",
                   help="Suppress import + outer namespace + helpers")
    args = p.parse_args()

    parts: list[str] = []
    if not args.no_preamble:
        parts.append(PREAMBLE)

    base = load_input_json(args.input)
    for spec in args.scenario:
        if ":" not in spec:
            print(f"--scenario expects 'kind:Namespace', got {spec!r}", file=sys.stderr)
            return 2
        kind, ns = spec.split(":", 1)
        if kind not in SCENARIOS:
            print(f"unknown scenario kind {kind!r}; valid: {sorted(SCENARIOS)}", file=sys.stderr)
            return 2
        j = copy.deepcopy(base)
        SCENARIOS[kind](j)
        parts.append(emit(ns, j))
        parts.append("")

    if not args.no_preamble:
        parts.append(POSTAMBLE)

    text = "\n".join(parts)
    if args.out:
        args.out.write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
