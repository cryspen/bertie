#!/usr/bin/env bash
# Run ProVerif on the extracted TLS 1.3 handshake (proofs/proverif/extraction,
# written by `./hax-driver.py extract-proverif`) and assert the expected query
# verdicts.
#
#   HAX_HOME : a hax checkout, for the ProVerif proof libraries.
set -uo pipefail
cd "$(dirname "$0")/../.."
HAX="${HAX_HOME:?set HAX_HOME to a hax checkout}"
PVLIB="$HAX/hax-lib/proof-libs/proverif"
PVD=proofs/proverif
EX="$PVD/extraction"

LIBS=(-lib "$PVLIB/primitives.pvl" -lib "$PVLIB/result.pvl" -lib "$PVLIB/cryptolib.pvl"
      -lib "$EX/missingdecl.pvl" -lib "$PVD/handwritten_lib.pvl"
      -lib "$EX/lib.pvl" -lib "$EX/model.pvl")

verdicts () { grep '^RESULT' "$1" | grep -oE 'is (true|false)' | awk '{print $2}' | tr '\n' ' '; }

rc=0
check () {
  local name=$1 file=$2 exp=$3 log got
  log=$(mktemp)
  proverif "${LIBS[@]}" "$EX/$file" > "$log" 2>&1
  got=$(verdicts "$log")
  echo "$name got: $got"
  echo "$name exp: $exp"
  if [ "$got" = "$exp" ]; then echo "$name: PASSED"; else echo "$name: FAILED"; grep -m3 -A3 Error "$log"; rc=1; fi
}

# Active (Dolev-Yao) attacker: the 7 security queries.
check active analysis.pv "false false false true false true true "
# Passive attacker: the honest handshake completes on its own, i.e. both
# completion events are reachable (`false`).
check passive analysis-passive.pv "false false "

exit $rc
