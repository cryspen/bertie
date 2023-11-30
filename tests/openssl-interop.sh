#!/bin/bash
# Simple interop to test that bertie works against OpenSSL
# TODO: #9 add s_client <-> bertie server

set -e

cwd=$(cd $(dirname $0); pwd -P)
openssl_cmd=${OPENSSL_CMD:-openssl}

openssl_version=$($openssl_cmd version)
if [[ $openssl_version != *"OpenSSL 3"* ]]; then
  echo "This script requires OpenSSL 3."
  echo "Set OPENSSL_CMD to your OpenSSL 3 binary."
  exit 1
fi

# start openssl server
$openssl_cmd s_server \
    -cert $cwd/assets/p256_cert.pem \
    -key $cwd/assets/p256_key.pem \
    -cipher ECDHE \
    -ciphersuites "TLS_AES_128_GCM_SHA256:TLS_CHACHA20_POLY1305_SHA256" \
    -port 6433 \
    -www &
pid=$(echo $!)

# run bertie client (auto closes after receiving http response)
cargo run -p simple_https_client -- 127.0.0.1 --port 6433

# kill openssl process
kill $pid
