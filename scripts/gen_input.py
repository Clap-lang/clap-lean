#!/usr/bin/env python3

# WARNING: This code is guaranteed to work only for the hardcoded JWT present, and is meant only to be used to provide a quick and easy way to run the full Keyless circuit. Detailed unit tests can be found in `circuit/src`.

# CLAP-LEAN: This file is a near-verbatim copy of upstream
#   doc/keyless-zk-proofs/circuit/tools/input_gen.py
# with a small set of localized modifications so we can generate fixtures
# beyond the single hardcoded JWT scenario. Every divergence from upstream
# is bracketed with `# CLAP: …` comments so a `diff -u` against upstream
# stays auditable. Configuration is collected in a single block near the
# top (search `# CLAP-CONFIG`).

import json
import os
from typing import Any

import jwt
from Crypto.Util.number import bytes_to_long
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.backends import default_backend as crypto_default_backend
import base64
from Crypto.PublicKey import RSA
from Crypto.Signature.pkcs1_15 import PKCS115_SigScheme
from Crypto.Hash import SHA256
import Crypto
import pprint

# CLAP: argparse for the new CLI driver.
import argparse

# ---------------------------------------------------------------------------
# CLAP-CONFIG: scenario selection and output knobs.
# ---------------------------------------------------------------------------
# A scenario controls the JWT payload, which JSON key becomes the uid, and
# which (optional) JSON key is exposed as the extra revealed field. Every
# downstream value (RSA signature, SHA padding, field indices, …) is then
# computed by the same upstream logic below.
#
# Pinned cryptographic values that EVERY scenario must respect because they
# are baked into the test ephemeral key triple `(temp_pubkey_*, jwt_randomness)`
# below — which Lean's KeylessTestFixture also pins:
#   - `iat`     = 1719866138
#   - `nonce`   = 2284473333442251804379681643965308154311773667525398119496797545594705356495
#                 (this is `Poseidon([temp_pubkey_*, temp_pubkey_len, exp_date, jwt_randomness])`)
# Any new scenario keeping the same epk triple MUST keep these two values.

CLAP_GOOGLE_JWT = {
    "iss":   "https://accounts.google.com",
    "azp":   "407408718192.apps.googleusercontent.com",
    "aud":   "407408718192.apps.googleusercontent.com",
    "sub":   "113990307082899718775",
    "email": "alice@gmail.com",
    "email_verified": True,
    "iat":   1719866138,
    "exp":   1719869738,
    "nonce": "2284473333442251804379681643965308154311773667525398119496797545594705356495",
}

CLAP_SCENARIOS = {
    # `default` reproduces upstream's hardcoded JWT and field choices
    # (uid_key="sub", extra_field="family_name"). Setting CLAP_JWT_DICT to
    # None means "use the upstream `original_b64` JWT verbatim", so the
    # diff against upstream is *zero* for this scenario.
    "default": {
        "jwt_dict":         None,
        "uid_key":          "sub",
        "extra_field_name": "family_name",
    },
    # `with_email` exercises `prove_request_with_email` from
    # prover_handler.rs: same Google iss/aud, uid_key="email", no extra
    # revealed field.
    "with_email": {
        "jwt_dict":         CLAP_GOOGLE_JWT,
        "uid_key":          "email",
        "extra_field_name": None,
    },
}


def _clap_parse_args():
    p = argparse.ArgumentParser(description=(
        "Generate a CIRCOM-format input.json for the keyless circuit. "
        "This is a localized fork of upstream input_gen.py with a single "
        "config block at the top; everything else mirrors upstream so a "
        "diff stays small and auditable."
    ))
    p.add_argument("--scenario", choices=sorted(CLAP_SCENARIOS),
                   default="default", help="Which scenario to generate.")
    p.add_argument("--out", default="input.json",
                   help="Output path for the generated JSON.")
    p.add_argument("--privkey", required=True,
                   help="Path to the RSA test private key (PEM) used to "
                        "sign the JWT. The canonical key is checked in at "
                        "keyless-zk-proofs/circuit/tools/test_rsa_privkey.pem.")
    return p.parse_args()


_clap_args = _clap_parse_args()
_clap_scenario = CLAP_SCENARIOS[_clap_args.scenario]
CLAP_JWT_DICT          = _clap_scenario["jwt_dict"]
CLAP_UID_KEY           = _clap_scenario["uid_key"]
CLAP_EXTRA_FIELD_NAME  = _clap_scenario["extra_field_name"]
CLAP_OUT               = _clap_args.out
CLAP_PRIVKEY           = _clap_args.privkey
# ---------------------------------------------------------------------------
# End CLAP-CONFIG. The rest of the file is the upstream input_gen.py with
# only the lines marked `# CLAP: …` modified.
# ---------------------------------------------------------------------------

def calc_string_bodies(string):
    string_bodies = [0] * len(string)
    string_bodies[1] = int(string[0] == '"')

    for i in range(2,len(string)):
        if not string_bodies[i-2] and string[i-1] == '"' and string[i-2] != '\\':
            string_bodies[i] = 1
        elif string_bodies[i-1] and string[i] == '"' and string[i-1] != '\\':
            string_bodies[i] = 0
        else:
            string_bodies[i] = string_bodies[i-1]
    return string_bodies

# Returns JSON array of bytes representing the input `string`, 0 padded to `maxLen`
def pad_string_new(string, maxLen, n="", use_ord=False):
    if use_ord:
        result = [ord(c) for c in string]
    else:
        result = [b for b in bytes(string, 'utf-8')]

    # pad to maxLen
    string_to_pad = maxLen - len(result)
    for i in range(string_to_pad):
        result.append(0)

    if "family_name" in string:
        print("family_name")

    result = json.dumps([str(x) for x in result], separators=(",", ":"))
    print(">>>N>", f"{n} '{string}'", f"'{result}'")
    if n:
        print("")  # f"len({n}): {len(result)}")
    return result


# Returns JSON array of bytes representing the input `string`, 0 padded to `maxLen`
def pad_string(string, maxLen, n="", use_ord=True):
    string_len = len(string)
    string_to_pad = maxLen - string_len

    result = "["
    for c in string:
        if use_ord:
            result = result + '"' + str(ord(c)) + '",'
        else:
            result = result + '"' + str(c) + '",'

    for i in range(string_to_pad):
        result = result + '"' + '0' + '",'

    result = result[:-1]  # remove last unnecessary ','
    result += "]"
    print(">>>O>", f"{n} '{string}'", f"'{result}'")
    return result

def format_output(dictionary):
    res = "{"
    for key in dictionary:
        res = res + key + " : " + str(dictionary[key]) + ","
    res = res[:-1] + "}"
    return res


MAX = 2048
BASE = 64


def long_to_limbs(n):
    '''Limbs are in l-endian.'''
    limbs = []
    for i in range(int(MAX / BASE)):  # split into 32 64-bit limbs
        idx = i * BASE

        limbs.append((n >> idx) & ((1 << BASE) - 1))

    return limbs


def limbs_to_long(limbs):
    val = 0
    base = 2 ** BASE
    for (i, l) in enumerate(limbs):
        val += l * (base ** i)

    return val


# iat_value = "1700255944" # Friday, November 17, 2023
iat_value = "1719866138"

exp_date_num = 111_111_111_111
exp_date = str(exp_date_num)  # 12-21-5490
exp_horizon_num = 999_999_999_999  # ~31,710 years
exp_horizon = str(exp_horizon_num)
# nonce_value = "2284473333442251804379681643965308154311773667525398119496797545594705356495"
nonce_value = "2284473333442251804379681643965308154311773667525398119496797545594705356495"
public_inputs_hash_value = '"' + str(
    990250399590304032496786539443088814495837679250179990478424822100531016130) + '"'

nonce = int(nonce_value)

jwt_max_len = 192 * 8

# jwt_dict = {
#  "iss": "test.oidc.provider",
#  "azp": "511276456880-i7i4787c1863damto6899ts989j2e35r.apps.googleusercontent.com",
#  "aud": "511276456880-i7i4787c1863damto6899ts989j2e35r.apps.googleusercontent.com",
#  "sub": "102904630171592520592",
#  "email": "hero1200091@gmail.com",
#  "email_verified": True,
#  "nonce": "12772123150809496860193457976937182964297283633705872391534946866719681904311",
#  "nbf": 1711552330,
#  "name": "コンドウハルキ",
#  "picture": "https://lh3.googleusercontent.com/a/ACg8ocIMZfIkNWGRBTD924xl_iefpMccLguwdMIinMPzaj5L4Q=s96-c",
#  "given_name": "ルキ",
#  "family_name": "コンドウ",
#  "iat": 1711552630,
#  "exp": 1911556230
# }

#jwt_dict = {
#        "iss":"https://accounts.google.com",
#        "azp":"407408718192.apps.googleusercontent.com",
#        "aud":"407408718192.apps.googleusercontent.com",
#        "sub":"113990307082899718775",
#        "at_hash":"lVeD4xP6Q1ZGrL3gFcCQLQ",
#        "name":"Michael Straka",
#        "picture":"https://lh3.googleusercontent.com/a/ACg8ocLVn8F8VnXKNNJhROhTpQuLLjFEdv_uhoe-DUaRTlxKEy9e4w=s96-c",
#        "given_name":"Michael",
#        "family_name":"Straka",
#        "iat":1719866138,
#        "exp":1719869738,
#        "nonce":"2284473333442251804379681643965308154311773667525398119496797545594705356495"
#        }


original_b64 = "eyJpc3MiOiJodHRwczovL2FjY291bnRzLmdvb2dsZS5jb20iLCJhenAiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJhdWQiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJzdWIiOiIxMTM5OTAzMDcwODI4OTk3MTg3NzUiLCJhdF9oYXNoIjoibFZlRDR4UDZRMVpHckwzZ0ZjQ1FMUSIsIm5hbWUiOiJNaWNoYWVsIFN0cmFrYSIsInBpY3R1cmUiOiJodHRwczovL2xoMy5nb29nbGV1c2VyY29udGVudC5jb20vYS9BQ2c4b2NMVm44RjhWblhLTk5KaFJPaFRwUXVMTGpGRWR2X3Vob2UtRFVhUlRseEtFeTllNHc9czk2LWMiLCJnaXZlbl9uYW1lIjoiTWljaGFlbCIsImZhbWlseV9uYW1lIjoiU3RyYWthIiwiaWF0IjoxNzE5ODY2MTM4LCJleHAiOjE3MTk4Njk3MzgsIm5vbmNlIjoiMjI4NDQ3MzMzMzQ0MjI1MTgwNDM3OTY4MTY0Mzk2NTMwODE1NDMxMTc3MzY2NzUyNTM5ODExOTQ5Njc5NzU0NTU5NDcwNTM1NjQ5NSJ9"
original_str = base64.urlsafe_b64decode(original_b64)
print("original_str bytes", original_str)
# CLAP: pick the JWT dict from the scenario; fall back to upstream's
# `original_b64`-decoded dict when the scenario asks for it (None).
jwt_dict = CLAP_JWT_DICT if CLAP_JWT_DICT is not None else json.loads(original_str)

#jwt_dict['iat'] = int(iat_value)  # WARNING: the code assumes this is NOT the last field
#jwt_dict['nonce'] = nonce_value  # WARNING: the code assumes this is the last field

secret = rsa.generate_private_key(
    backend=crypto_default_backend(),
    public_exponent=65537,
    key_size=2048
)

#class MyPyJWT(jwt.PyJWT):
#    def _encode_payload(
#            self,
#            payload: dict[str, Any],
#            headers: dict[str, Any] | None = None,
#            json_encoder: type[json.JSONEncoder] | None = None,
#    ) -> bytes:
#        return original_str  # json.dumps(payload, separators=(",", ":"), ).encode("utf-8")


signed_b64_jwt_string = jwt.encode(jwt_dict, secret, algorithm="RS256", headers={"kid": "test_jwk"})
#signed_b64_jwt_string = MyPyJWT().encode(jwt_dict, secret, algorithm="RS256", headers={"kid": "test_jwk"})
unsigned_b64_jwt_string = signed_b64_jwt_string[:signed_b64_jwt_string.rfind(".")]

# public_key = secret.public_key().public_bytes(
#    crypto_serialization.Encoding.OpenSSH,
#    crypto_serialization.PublicFormat.OpenSSH
# )
jwt_payload_b64 = unsigned_b64_jwt_string[unsigned_b64_jwt_string.rfind(".") + 1:]
print(jwt_payload_b64)
# CLAP: base64url JWTs omit `=` padding; restore it for Python's strict decoder
# (upstream relies on `original_b64` having matching padding, which is not
# guaranteed for re-encoded jwt_dicts).
jwt_payload = base64.urlsafe_b64decode(jwt_payload_b64 + "=" * (-len(jwt_payload_b64) % 4))
jwt_payload = jwt_payload.decode('utf-8')
print("\njwt_payload bytes  ", jwt_payload, "\n")
jwt_max_header_len = 300
jwt_header_string = unsigned_b64_jwt_string[:unsigned_b64_jwt_string.find(".") + 1]

header_value = pad_string(jwt_header_string, jwt_max_header_len)

header_len_with_separator_value = '"' + str(len(jwt_header_string)) + '"'

maxAudKVPairLen = 140
maxAudNameLen = 40
maxAudValueLen = 120
# CLAP: derive aud from jwt_dict so non-default scenarios with a different
# `aud` produce correct field bytes (upstream hardcoded the Google
# clientID, which only happens to also match our scenarios).
aud_field_string = "\"aud\":\"" + jwt_dict['aud'] + "\","
#aud_field_string = "\"aud\":\"511276456880-i7i4787c1863damto6899ts989j2e35r.apps.googleusercontent.com\","
aud_string_bodies = calc_string_bodies(aud_field_string)
aud_string_bodies_value = pad_string(aud_string_bodies, maxAudKVPairLen, use_ord=False)
aud_field_value = pad_string(aud_field_string, maxAudKVPairLen)
aud_field_len_value = '"' + str(len(aud_field_string)) + '"'
aud_index_value = '"' + str(jwt_payload.index("aud") - 1) + '"'  # First '"' character in aud field index in payload
aud_colon_index = aud_field_string.index(":")
aud_colon_index_value = '"' + str(aud_colon_index) + '"'
aud_value_index_value = '"' + str(aud_colon_index + 2) + '"'  # TODO: This doesn't work if there's whitespace
aud_name = "aud"
# CLAP: see comment on `aud_field_string` above.
aud_value = jwt_dict['aud']
#aud_value = "511276456880-i7i4787c1863damto6899ts989j2e35r.apps.googleusercontent.com"
aud_name_value = pad_string(aud_name, maxAudNameLen)
aud_value_value = pad_string(aud_value, maxAudValueLen)
aud_value_len_value = '"' + str(len(aud_value)) + '"'

private_aud_value_value = aud_value_value
override_aud_value_value = pad_string("", maxAudValueLen)
private_aud_value_len_value = aud_value_len_value
override_aud_value_len_value = '"' + "0" + '"'
use_aud_override_value = '"' + "0" + '"'
skip_aud_checks_value = '"' + "0" + '"'

maxIatKVPairLen = 50
maxIatNameLen = 10
maxIatValueLen = 45
iat_field_string = "\"iat\":" + iat_value + ","
print("iat_field_string")
print(iat_field_string)
iat_field_value = pad_string(iat_field_string, maxIatKVPairLen)
iat_field_len_value = '"' + str(len(iat_field_string)) + '"'
iat_index_value = '"' + str(jwt_payload.index("iat") - 1) + '"'  # First '"' character in aud field index in payload
iat_colon_index = iat_field_string.index(":")
iat_colon_index_value = '"' + str(iat_colon_index) + '"'
iat_value_index_value = '"' + str(iat_colon_index + 1) + '"'  # TODO: This doesn't work if there's whitespace
iat_name = "iat"
iat_name_value = pad_string(iat_name, maxIatNameLen)
iat_value_value = pad_string(iat_value, maxIatValueLen)
iat_value_len_value = '"' + str(len(iat_value)) + '"'
exp_date_value = '"' + exp_date + '"'
exp_horizon_value = '"' + exp_horizon + '"'

maxUidKVPairLen = 350
maxUidNameLen = 30
maxUidValueLen = 330
# CLAP: parameterize uid_key (sub vs email) so we can drive
# `prove_request_with_email`. Upstream hardcodes "sub" + the matching
# value; we read both from the scenario config + jwt_dict.
uid_field_string = "\"" + CLAP_UID_KEY + "\":\"" + jwt_dict[CLAP_UID_KEY] + "\","
#uid_field_string = "\"sub\":\"102904630171592520592\","
uid_string_bodies = calc_string_bodies(uid_field_string)
uid_string_bodies_value = pad_string(uid_string_bodies, maxUidKVPairLen, use_ord=False)
uid_field_value = pad_string(uid_field_string, maxUidKVPairLen)
uid_field_len_value = '"' + str(len(uid_field_string)) + '"'
# CLAP: index of `uid_key` (not necessarily "sub").
uid_index_value = '"' + str(jwt_payload.index(CLAP_UID_KEY) - 1) + '"'

# CLAP: uid_name length comes from the scenario.
uid_name_len_value = '"' + str(len(CLAP_UID_KEY)) + '"'
uid_colon_index = uid_field_string.index(":")
uid_colon_index_value = '"' + str(uid_colon_index) + '"'
uid_value_index_value = '"' + str(uid_colon_index + 2) + '"'
# CLAP: name + value driven by scenario + jwt_dict.
uid_name = CLAP_UID_KEY
uid_value = jwt_dict[CLAP_UID_KEY]
#uid_value = "102904630171592520592"
uid_name_value = pad_string(uid_name, maxUidNameLen)
uid_value_value = pad_string(uid_value, maxUidValueLen)
uid_value_len_value = '"' + str(len(uid_value)) + '"'

# Extra revealed public JWT field
maxEFKVPairLen = 350
maxEFNameLen = 30
maxEFValueLen = 330
# CLAP: parameterize the extra field. When the scenario sets it to None
# (i.e. `prove_request_with_no_extra_field`), we still emit a non-empty
# placeholder because `verifyExtraField` requires `substr.len > 0` even
# though the result is later gated by `useExtraField=0`. We re-use
# `email_verified` as the placeholder to keep the bytes innocuous.
if CLAP_EXTRA_FIELD_NAME is not None:
    _clap_extra_name = CLAP_EXTRA_FIELD_NAME
    _clap_extra_value = jwt_dict[CLAP_EXTRA_FIELD_NAME]
    _clap_extra_field_string = "\"" + _clap_extra_name + "\":\"" + _clap_extra_value + "\","
else:
    # placeholder, gated out by use_extra_field=0
    _clap_extra_name = "email_verified"
    _clap_extra_value = "true"
    _clap_extra_field_string = "\"email_verified\":true,"
# CLAP: use_extra_field is hardcoded to "0" to match upstream's behaviour
# verbatim. Upstream always emits "0" regardless of whether the extra-field
# bytes are populated. A future scenario that wants to enable verification
# of the extra field can lift this constant.
_clap_use_extra = "0"
extra_field_string = _clap_extra_field_string
extra_field_value = pad_string_new(extra_field_string, maxEFKVPairLen)
extra_field_len_value = '"' + str(len(extra_field_string)) + '"'
extra_index_value = '"' + str(jwt_payload.index(_clap_extra_name) - 1) + '"'

extra_name_len_value = '"' + str(len(_clap_extra_name)) + '"'
extra_colon_index = extra_field_string.index(":")
extra_colon_index_value = '"' + str(extra_colon_index) + '"'
extra_value_index_value = '"' + str(extra_colon_index + 2) + '"'
extra_name = _clap_extra_name
extra_value = _clap_extra_value
#extra_value = "コンドウ"
extra_name_value = pad_string_new(extra_name, maxEFNameLen)
extra_value_value = pad_string_new(extra_value, maxEFValueLen)
extra_value_len_value = '"' + str(len(extra_value)) + '"'
use_extra_field_value = '"' + _clap_use_extra + '"'

maxEVKVPairLen = 30
maxEVNameLen = 20
maxEVValueLen = 10
ev_field_string = "\"email_verified\":true,"
ev_field_value = pad_string(ev_field_string, maxEVKVPairLen)
ev_field_len_value = '"' + str(len(ev_field_string)) + '"'
# CLAP: locate `email_verified` in the JWT payload (or 0 if absent —
# `verifyEvField`'s checks are gated by uidIsEmail when uid_key != email).
ev_index_value = '"' + str(jwt_payload.index("email_verified") - 1
                            if "email_verified" in jwt_payload else 0) + '"'

ev_colon_index = 16
ev_colon_index_value = '"' + str(ev_colon_index) + '"'
ev_value_index_value = '"' + str(ev_colon_index + 1) + '"'  # TODO: Doesn't work with whitespace
ev_name = "email_verified"
ev_value = "true"
ev_name_value = pad_string(ev_name, maxEVNameLen)
ev_value_value = pad_string(ev_value, maxEVValueLen)
ev_value_len_value = '"' + str(len(ev_value)) + '"'

maxIssKVPairLen = 140
maxIssNameLen = 40
maxIssValueLen = 120
# CLAP: derive iss from jwt_dict (matches upstream string for default).
iss_field_string = "\"iss\":\"" + jwt_dict['iss'] + "\","
#iss_field_string = "\"iss\":\"test.oidc.provider\","
iss_string_bodies = calc_string_bodies(iss_field_string)
iss_string_bodies_value = pad_string(iss_string_bodies, maxIssKVPairLen, use_ord=False)
iss_field_value = pad_string(iss_field_string, maxIssKVPairLen)
iss_field_len_value = '"' + str(len(iss_field_string)) + '"'
iss_index_value = '"' + str(jwt_payload.index("iss") - 1) + '"'

iss_colon_index = iss_field_string.index(":")
iss_colon_index_value = '"' + str(iss_colon_index) + '"'
iss_value_index_value = '"' + str(iss_colon_index + 2) + '"'  # TODO: Doesn't work with whitespace
iss_name = "iss"
# CLAP: derive iss value from jwt_dict (matches upstream string for default).
iss_value = jwt_dict['iss']
#iss_value = "test.oidc.provider"
iss_name_value = pad_string(iss_name, maxIssNameLen)
iss_value_value = pad_string(iss_value, maxIssValueLen)
iss_value_len_value = '"' + str(len(iss_value)) + '"'

# Values used in nonce
temp_pubkey_0 = 242984842061174104272170180221318235913385474778206477109637294427650138112
temp_pubkey_1 = 4497911
temp_pubkey_2 = 0
temp_pubkey_len = 34
jwt_randomness = 42
nonce_bitstring = format(nonce, 'b')
temp_pubkey_value = "[ \"" + str(temp_pubkey_0) + '"' + ',\"' + str(temp_pubkey_1) + '"' + ',\"' + str(
    temp_pubkey_2) + '"]'
temp_pubkey_len_value = '"' + str(temp_pubkey_len) + '"'
jwt_randomness_value = '"' + str(jwt_randomness) + '"'

maxNonceKVPairLen = 105
maxNonceNameLen = 10
maxNonceValueLen = 100
nonce_field_string = "\"nonce\":\"" + nonce_value + "\"}"
nonce_string_bodies = calc_string_bodies(nonce_field_string)
nonce_string_bodies_value = pad_string(nonce_string_bodies, maxNonceKVPairLen, use_ord=False)
nonce_field_value = pad_string(nonce_field_string, maxNonceKVPairLen)
nonce_field_len_value = '"' + str(len(nonce_field_string)) + '"'
nonce_index_value = '"' + str(jwt_payload.index("nonce") - 1) + '"'

nonce_colon_index = nonce_field_string.index(":")
nonce_colon_index_value = '"' + str(nonce_colon_index) + '"'
nonce_value_index_value = '"' + str(nonce_colon_index + 2) + '"'  # TODO: Doesn't work with whitespace
nonce_name = "nonce"
nonce_value_reversed = nonce_value[::-1]
nonce_name_value = pad_string(nonce_name, maxNonceNameLen)
nonce_value_value = pad_string(nonce_value, maxNonceValueLen)
nonce_value_len_value = '"' + str(len(nonce_value)) + '"'

pepper = 76
pepper_value = '"' + str(pepper) + '"'

jwt_payload_string_no_padding = unsigned_b64_jwt_string[unsigned_b64_jwt_string.find(".") + 1:]
print("\n\n")
print("original_b64 payload         ", original_b64)
print("jwt_payload_string_no_padding", jwt_payload_string_no_padding)

print("original_b64 bytes                 ", base64.urlsafe_b64decode(original_b64))
# CLAP: same `=`-padding restoration as above.
print("jwt_payload_string_no_padding bytes",
      base64.urlsafe_b64decode(jwt_payload_string_no_padding
                               + "=" * (-len(jwt_payload_string_no_padding) % 4)))
print("\n\n")

jwt_max_payload_len = 192 * 8 - 64

jwt_payload_string_no_padding_value = pad_string(jwt_payload_string_no_padding, jwt_max_payload_len,
                                                 n="jwt_payload_string_no_padding_value")

payload_len = len(jwt_payload_string_no_padding)
payload_len_value = '"' + str(payload_len) + '"'

# Add SHA2 padding to the end of the b64 jwt string
unsigned_b64_jwt_bits = ""
for c in unsigned_b64_jwt_string:
    bits = bin(ord(c))
    bits = bits[2:].zfill(8)
    unsigned_b64_jwt_bits += bits

L = len(unsigned_b64_jwt_bits)

# Used as circuit input
L_bit_encoded = format(L, 'b').zfill(64)
print("L_bit_encoded: ", L_bit_encoded)

L_byte_encoded = ""
for i in range(8):
    idx = i * 8
    bits = L_bit_encoded[idx:idx + 8]
    ascii_char = chr(int(bits, 2))
    L_byte_encoded += ascii_char

print("L_byte_encoded: ", L_byte_encoded.encode('utf-8'))
L_byte_encoded_value = pad_string(L_byte_encoded, 8, n="L_byte_encoded_value", use_ord=True)

L_mod = L % 512
# https://www.rfc-editor.org/rfc/rfc4634.html#section-4.1
# 4.1.a append '1'
unsigned_b64_jwt_bits += '1'

# 4.1.b Append 'K' 0s where K is the smallest non-negative integer solution to L+1+K = 448 mod 512, and L is the length of the message in bits
K = 448 - L_mod - 1

# Used as a circuit input
padding_without_len = '1' + '0' * K
padding_without_len = padding_without_len.ljust(512, '0')

padding_without_len_bytes = ""
for i in range(64):
    idx = i * 8
    bits = padding_without_len[idx:idx + 8]
    ascii_char = chr(int(bits, 2))
    padding_without_len_bytes += ascii_char

padding_without_len_bytes_value = pad_string(padding_without_len_bytes, 64, n="padding_without_len_bytes", use_ord=True)

unsigned_b64_jwt_bits_sha_padded = unsigned_b64_jwt_bits + '0' * K

# 4.1.c Append L in binary form as 64 bits
L_bits = format(L, 'b').zfill(64)

unsigned_b64_jwt_bits_sha_padded += L_bits

unsigned_b64_jwt_string_sha_padded = ""
for i in range(int(len(unsigned_b64_jwt_bits_sha_padded) / 8)):
    idx = i * 8
    bits = unsigned_b64_jwt_bits_sha_padded[idx:idx + 8]
    ascii_char = chr(int(bits, 2))
    unsigned_b64_jwt_string_sha_padded += ascii_char

print("unsigned_b64_jwt_bits_sha_padded", unsigned_b64_jwt_bits_sha_padded)

jwt_value = pad_string(unsigned_b64_jwt_string_sha_padded, jwt_max_len, n="jwt_value")

jwt_num_sha2_blocks = int((len(unsigned_b64_jwt_string_sha_padded) * 8) / 512)  # SHA2 uses 512-bit blocks
jwt_num_sha2_blocks_value = '"' + str(jwt_num_sha2_blocks) + '"'

jwt_payload_string = unsigned_b64_jwt_string_sha_padded[unsigned_b64_jwt_string_sha_padded.find(".") + 1:]

payload_value = pad_string(jwt_payload_string, jwt_max_payload_len)

# Compute RSA signature over the full unsigned JWT
# CLAP: read the private key from the configured path (upstream uses
# a relative path that only works from `circuit/`).
with open(CLAP_PRIVKEY, 'rb') as f:
    privkey_str = f.read()
    f.close()
keyPair = Crypto.PublicKey.RSA.import_key(privkey_str)
# keyPair = RSA.generate(bits=2048)


jwt_byte_encoding = str.encode(unsigned_b64_jwt_string)
hash = SHA256.new(jwt_byte_encoding)
signer = PKCS115_SigScheme(keyPair)
signature = signer.sign(hash)

sig_long = bytes_to_long(signature)
sig_limbs = long_to_limbs(sig_long)
##print(limbs_to_long(sig_limbs) == sig_long)
sig_value = "["
for l in sig_limbs:
    sig_value += '"' + str(l) + '"' + ","
sig_value = sig_value[:-1] + "]"

mod_limbs = long_to_limbs(keyPair.n)
##print(limbs_to_long(mod_limbs) == keyPair.n)

mod_value = "["
for l in mod_limbs:
    mod_value += '"' + str(l) + '"' + ","
mod_value = mod_value[:-1] + "]"

hash_limbs = long_to_limbs(bytes_to_long(hash.digest()))[:4]
##print(hash_limbs)

json_dict = {
    "\"jwt\"": jwt_value,
    "\"jwt_header_with_separator\"": header_value,
    "\"jwt_payload\"": payload_value,
    "\"public_inputs_hash\"": public_inputs_hash_value,
    "\"header_len_with_separator\"": header_len_with_separator_value,
    "\"signature\"": sig_value,
    "\"pubkey_modulus\"": mod_value,
    "\"aud_field\"": aud_field_value,
    "\"aud_field_string_bodies\"": aud_string_bodies_value,
    "\"aud_field_len\"": aud_field_len_value,
    "\"aud_index\"": aud_index_value,
    "\"aud_value_index\"": aud_value_index_value,
    "\"aud_colon_index\"": aud_colon_index_value,
    "\"aud_name\"": aud_name_value,
    "\"uid_field\"": uid_field_value,
    "\"uid_field_string_bodies\"": uid_string_bodies_value,
    "\"uid_field_len\"": uid_field_len_value,
    "\"uid_index\"": uid_index_value,
    "\"uid_name_len\"": uid_name_len_value,
    "\"uid_value_index\"": uid_value_index_value,
    "\"uid_value_len\"": uid_value_len_value,
    "\"uid_colon_index\"": uid_colon_index_value,
    "\"uid_name\"": uid_name_value,
    "\"uid_value\"": uid_value_value,
    "\"ev_field\"": ev_field_value,
    "\"ev_field_len\"": ev_field_len_value,
    "\"ev_index\"": ev_index_value,
    "\"ev_value_index\"": ev_value_index_value,
    "\"ev_value_len\"": ev_value_len_value,
    "\"ev_colon_index\"": ev_colon_index_value,
    "\"ev_name\"": ev_name_value,
    "\"ev_value\"": ev_value_value,
    "\"iss_field\"": iss_field_value,
    "\"iss_field_string_bodies\"": iss_string_bodies_value,
    "\"iss_field_len\"": iss_field_len_value,
    "\"iss_index\"": iss_index_value,
    "\"iss_value_index\"": iss_value_index_value,
    "\"iss_value_len\"": iss_value_len_value,
    "\"iss_colon_index\"": iss_colon_index_value,
    "\"iss_name\"": iss_name_value,
    "\"iss_value\"": iss_value_value,
    "\"nonce_field\"": nonce_field_value,
    "\"nonce_field_string_bodies\"": nonce_string_bodies_value,
    "\"nonce_field_len\"": nonce_field_len_value,
    "\"nonce_index\"": nonce_index_value,
    "\"nonce_value_index\"": nonce_value_index_value,
    "\"nonce_value_len\"": nonce_value_len_value,
    "\"nonce_colon_index\"": nonce_colon_index_value,
    "\"nonce_name\"": nonce_name_value,
    "\"nonce_value\"": nonce_value_value,
    "\"temp_pubkey\"": temp_pubkey_value,
    "\"jwt_randomness\"": jwt_randomness_value,
    "\"pepper\"": pepper_value,
    "\"jwt_num_sha2_blocks\"": jwt_num_sha2_blocks_value,
    "\"iat_field\"": iat_field_value,
    "\"iat_field_len\"": iat_field_len_value,
    "\"iat_index\"": iat_index_value,
    "\"iat_value_index\"": iat_value_index_value,
    "\"iat_value_len\"": iat_value_len_value,
    "\"iat_colon_index\"": iat_colon_index_value,
    "\"iat_name\"": iat_name_value,
    "\"iat_value\"": iat_value_value,
    "\"exp_date\"": exp_date_value,
    "\"exp_delta\"": exp_horizon_value,
    "\"b64_payload_len\"": payload_len_value,
    "\"jwt_len_bit_encoded\"": L_byte_encoded_value,
    "\"padding_without_len\"": padding_without_len_bytes_value,
    "\"temp_pubkey_len\"": temp_pubkey_len_value,
    "\"private_aud_value\"": private_aud_value_value,
    "\"override_aud_value\"": override_aud_value_value,
    "\"private_aud_value_len\"": private_aud_value_len_value,
    "\"override_aud_value_len\"": override_aud_value_len_value,
    "\"use_aud_override\"": use_aud_override_value,
    "\"extra_field\"": extra_field_value,
    "\"extra_field_len\"": extra_field_len_value,
    "\"extra_index\"": extra_index_value,
    "\"jwt_payload_without_sha_padding\"": jwt_payload_string_no_padding_value,
    "\"use_extra_field\"": use_extra_field_value,
    "\"skip_aud_checks\"": skip_aud_checks_value
}
inputs_dot_json = format_output(json_dict)

# print(inputs_dot_json)
# CLAP: write to the configured output path instead of the hardcoded
# `input.json` (and remove only that path, not whatever the user gave us).
print(f"Writing circuit inputs to {CLAP_OUT}...")
if os.path.exists(CLAP_OUT):
    os.remove(CLAP_OUT)
f = open(CLAP_OUT, "a")
f.write(inputs_dot_json)
f.close()
# print(format(int(binascii.hexlify(hash.digest()),16), 'b'))
##print(K)
# os.remove("privkey.pem")
# privkeyfile = open("privkey.pem", "wb")
# privkeyfile.write(keyPair.exportKey("PEM"))
# privkeyfile.close()

##print("signed jwt: " + signed_b64_jwt_string)
##print("unsigned signed jwt: " + unsigned_b64_jwt_string)
##print(ev_colon_index)
##print(ev_value_index_value)

print("Results")
print("-------")

print("\nIssued at:")
print(iat_value)

print("\nExpiration date:")
print(exp_date)

print("\nExpiration horizon:")
print(exp_horizon)

print("\nPepper")
print(pepper)

print("\nExtra field")
print(extra_field_string)

print("\nEPK blinder (JWT randomness)")
print(jwt_randomness_value)

print("\nbase64url-encoded RSA modulus")
modulus_bytes = keyPair.n.to_bytes((keyPair.n.bit_length() + 7) // 8, byteorder='big')
print(base64.urlsafe_b64encode(modulus_bytes))

print("\nPublic inputs hash")
print(public_inputs_hash_value)

print("\nbase64url-encoded JWT header:")
print(jwt_header_string[:-1])

print("\nDecoded JWT header:")
print(base64.urlsafe_b64decode(jwt_header_string[:-1] + "=="))

print("\nDecoded JWT payload:")
print(jwt_payload)

print("\nPretty-printed JWT payload:")
jwt_parsed = json.loads(jwt_payload)
