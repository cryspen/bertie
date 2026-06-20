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
PVD=proofs/proverif
eval "$(opam env --switch=hax-proverif 2>/dev/null)" 2>/dev/null || true
if ! command -v cargo-hax >/dev/null 2>&1; then export PATH="$ENG/target/release:$PATH"; fi
export HAX_RUST_ENGINE_BINARY="${HAX_RUST_ENGINE_BINARY:-$ENG/target/release/hax-rust-engine}"
INC='-** +~**::tls13handshake::** +~**::server::lookup_db +~**::tls13utils::parse_failed +!**::tls13utils::concat_inner +!**::tls13utils::eq_inner +!**::tls13utils::check_eq_inner +!**::tls13formats::handshake_data::to_bytes_inner +!**::tls13formats::handshake_data::to_two_inner +!**::tls13formats::handshake_data::to_four_inner +!**::tls13crypto::hash +~**::tls13keyscheduler::derive_hk_ms +~**::tls13keyscheduler::derive_finished_key +~**::tls13keyscheduler::derive_hk_handles +~**::tls13keyscheduler::derive_aead_key_iv +~**::tls13keyscheduler::key_schedule::no_psk +~**::tls13keyscheduler::key_schedule::tagkey_from_handle +!**::tls13record::encrypt_handshake +!**::tls13record::decrypt_handshake'
cargo hax -C -p bertie --no-default-features --features hax-pv,std ';' into -i "$INC" proverif
# de-dup the auto-declared `missingdecl` against the real defs and mark the
# survivors `[data]` (opaque constructors must be matchable in patterns).
python3 - "$PRIM" "$PVD/handwritten_lib.pvl" "$PVD/extraction/lib.pvl" "$PVD/extraction/missingdecl.pvl" > "$PVD/extraction/missingdecl.dedup.pvl" <<'PY'
import re,sys
defs=set()
for f in sys.argv[1:4]:
    try: t=open(f).read()
    except: continue
    for m in re.finditer(r'^(?:fun|letfun|const)\s+([A-Za-z0-9_]+)', t, re.M): defs.add(m.group(1))
    for m in re.finditer(r';\s*([A-Za-z0-9_]+)\s*\(', t.replace('\n',' ')): defs.add(m.group(1))
out=[]
for l in open(sys.argv[4]):
    m=re.match(r'^(fun|const)\s+([A-Za-z0-9_]+)', l)
    if m and m.group(2) in defs: continue
    if l.startswith('fun ') and l.rstrip().endswith(': bitstring.'): l=l.rstrip()[:-1]+' [data].\n'
    out.append(l)
sys.stdout.write(''.join(out))
PY
LOG=$(mktemp)
proverif -lib "$PRIM" -lib "$PVD/extraction/missingdecl.dedup.pvl" -lib "$PVD/handwritten_lib.pvl" -lib "$PVD/extraction/lib.pvl" "$PVD/extraction/analysis.pv" > "$LOG" 2>&1
got=$(grep '^RESULT' "$LOG" | grep -oE 'is (true|false)' | awk '{print $2}' | tr '\n' ' ')
exp="false false false true false true true "
echo "  got: $got"
echo "  exp: $exp"
if [ "$got" = "$exp" ]; then echo "CHECK PASSED (7/7)"; else echo "CHECK FAILED"; grep -m1 Error "$LOG"; exit 1; fi
