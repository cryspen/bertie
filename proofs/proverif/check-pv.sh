#!/usr/bin/env bash
# Re-extract the bertie TLS 1.3 handshake to ProVerif via the hax proverif-rust
# backend, compose it with the de-duplicated missingdecl, run ProVerif, and
# assert the 7 expected query verdicts.
#
#   HAX_PROVERIF_DIR : a hax checkout @ proverif-rust-backend (>= commit with the
#                      Result::Err / all-wild-pattern / reductive-nat-add fixes).
#                      Its target/release must be built (or the hax-proverif opam
#                      switch installed via setup-local.sh).
set -uo pipefail
cd "$(dirname "$0")/../.."
ENG="${HAX_PROVERIF_DIR:?set HAX_PROVERIF_DIR to a hax checkout}"
PRIM="$ENG/hax-lib/proof-libs/proverif/primitives.pvl"
CRYPTO="$ENG/hax-lib/proof-libs/proverif/cryptolib.pvl"
PVD=proofs/proverif
eval "$(opam env --switch=hax-proverif 2>/dev/null)" 2>/dev/null || true
if ! command -v cargo-hax >/dev/null 2>&1; then export PATH="$ENG/target/release:$PATH"; fi
export HAX_RUST_ENGINE_BINARY="${HAX_RUST_ENGINE_BINARY:-$ENG/target/release/hax-rust-engine}"
INC='-** +~**::tls13handshake::** +~**::server::lookup_db +~**::tls13utils::parse_failed +!**::tls13utils::concat_inner +!**::tls13utils::eq_inner +!**::tls13utils::check_eq_inner +!**::tls13formats::handshake_data::to_bytes_inner +!**::tls13formats::handshake_data::to_two_inner +!**::tls13formats::handshake_data::to_four_inner +!**::tls13crypto::hash +~**::tls13keyscheduler::derive_hk_ms +~**::tls13keyscheduler::derive_finished_key +~**::tls13keyscheduler::derive_hk_handles +~**::tls13keyscheduler::derive_aead_key_iv +~**::tls13keyscheduler::key_schedule::no_psk +~**::tls13keyscheduler::key_schedule::tagkey_from_handle +!**::tls13record::encrypt_handshake +!**::tls13record::decrypt_handshake'
cargo hax -C -p bertie --no-default-features --features hax-pv,std ';' into -i "$INC" proverif
# de-dup the auto-declared `missingdecl` against the real defs and mark the
# survivors `[data]` (opaque constructors must be matchable in patterns).
python3 - "$PRIM" "$CRYPTO" "$PVD/handwritten_lib.pvl" "$PVD/extraction/lib.pvl" "$PVD/extraction/missingdecl.pvl" > "$PVD/extraction/missingdecl.dedup.pvl" <<'PY'
import re,sys
defs=set()
for f in sys.argv[1:5]:
    try: t=open(f).read()
    except: continue
    for m in re.finditer(r'^(?:fun|letfun|const)\s+([A-Za-z0-9_]+)', t, re.M): defs.add(m.group(1))
    for m in re.finditer(r';\s*([A-Za-z0-9_]+)\s*\(', t.replace('\n',' ')): defs.add(m.group(1))
out=[]
for l in open(sys.argv[5]):
    m=re.match(r'^(fun|const)\s+([A-Za-z0-9_]+)', l)
    if m and m.group(2) in defs: continue
    if l.startswith('fun ') and l.rstrip().endswith(': bitstring.'): l=l.rstrip()[:-1]+' [data].\n'
    out.append(l)
sys.stdout.write(''.join(out))
PY
# The handwritten model (tables, events, ciphersuites, Client/Server/...
# role processes) lives in model.pvl and is shared by both the active and the
# passive harness.
LIBS=(-lib "$PRIM" -lib "$CRYPTO" -lib "$PVD/extraction/missingdecl.dedup.pvl" -lib "$PVD/handwritten_lib.pvl" -lib "$PVD/extraction/lib.pvl" -lib "$PVD/extraction/model.pvl")

verdicts () { grep '^RESULT' "$1" | grep -oE 'is (true|false)' | awk '{print $2}' | tr '\n' ' '; }

rc=0

# --- Active (Dolev-Yao) attacker: the 7 security queries (analysis.pv). ---
LOG=$(mktemp)
proverif "${LIBS[@]}" "$PVD/extraction/analysis.pv" > "$LOG" 2>&1
got=$(verdicts "$LOG")
exp="false false false true false true true "
echo "active  got: $got"
echo "active  exp: $exp"
if [ "$got" = "$exp" ]; then echo "ACTIVE CHECK PASSED (7/7)"; else echo "ACTIVE CHECK FAILED"; grep -m1 Error "$LOG"; rc=1; fi

# --- Passive attacker: the honest handshake must run to completion without
#     any help from the attacker, i.e. both completion events stay reachable
#     (analysis-passive.pv). A `false` verdict means "reachable". ---
PLOG=$(mktemp)
proverif "${LIBS[@]}" "$PVD/extraction/analysis-passive.pv" > "$PLOG" 2>&1
pgot=$(verdicts "$PLOG")
pexp="false false "
echo "passive got: $pgot"
echo "passive exp: $pexp (ClientFinishedHandshake + ServerFinishedHandshake reachable)"
if [ "$pgot" = "$pexp" ]; then echo "PASSIVE CHECK PASSED (2/2 reachable)"; else echo "PASSIVE CHECK FAILED"; grep -m1 Error "$PLOG"; rc=1; fi

exit $rc
