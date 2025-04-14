#!/bin/bash
# Run the bogo interop runner.
# Bogo is expected in ${BORINGSSL_ROOT}/ssl/test/runner.
# A specific test can be run by passing in -test "Test1;Test2".
# To run a disabled test pass -include-disabled in as well.

set -e

if [ -z ${BORINGSSL_ROOT} ]; then
    echo "Please set BORINGSSL_ROOT to the root of boringssl."
    exit 1
fi

cwd=$(cd $(dirname $0); pwd -P)

# Build t13 bogo shim
cargo build -p bogo_shim --no-default-features

# Run bogo runner
(cd ${BORINGSSL_ROOT}/ssl/test/runner && \
  go test \
    -shim-path $cwd/../target/debug/bogo_shim \
    -shim-config $cwd/assets/config.json \
    -allow-unimplemented \
    "$@")
