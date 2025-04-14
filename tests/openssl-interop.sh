#!/bin/bash
# Interop to test that t13 works against OpenSSL

set -e

cwd=$(
  cd $(dirname $0)
  pwd -P
)
openssl_cmd=${OPENSSL_CMD:-openssl}

openssl_version=$($openssl_cmd version)
if [[ $openssl_version != *"OpenSSL 3"* ]]; then
  echo "This script requires OpenSSL 3."
  echo "Set OPENSSL_CMD to your OpenSSL 3 binary."
  exit 1
fi

# # === OpenSSL Server <-> t13 Client ===

print_success() {
  if [ $? -eq 0 ]; then
    echo "    success"
  else
    echo "    failed"
  fi
}

run_openssl() {
  # start openssl server
  $openssl_cmd s_server \
    -cert $cwd/assets/$1_cert.pem \
    -key $cwd/assets/$1_key.pem \
    -cipher ECDHE \
    -curves P-256:X25519 \
    -ciphersuites "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA256:TLS_CHACHA20_POLY1305_SHA256" \
    -port 6443 \
    -www &
  pid=$!
  # give the server time to start up
  sleep 2
}

t13_client_test() {
  # ECDH Server cert
  echo "Running OpenSSL Server with ECDSA P256 certificate"
  run_openssl p256

  # run t13 client (auto closes after receiving http response)
  echo "  Connecting with t13 Client | Chacha20Poly1305 x25519"
  RUST_LOG=none cargo run -p simple_https_client -- localhost --port 6443 --ciphersuite SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519 2>/dev/null
  print_success
  echo "  Connecting with t13 Client | Chacha20Poly1305 P256"
  RUST_LOG=none cargo run -p simple_https_client -- localhost --port 6443 --ciphersuite SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256 2>/dev/null
  print_success

  # kill openssl process
  echo "  Killing the OpenSSL Server"
  kill $pid

  # ECDH Server cert
  echo "Running OpenSSL Server with RSA PSS certificate"
  run_openssl rsa

  echo "  Connecting with t13 Client | Chacha20Poly1305 x25519"
  RUST_LOG=none cargo run -p simple_https_client -- localhost --port 6443 --ciphersuite SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519 2>/dev/null
  print_success
  echo "  Connecting with t13 Client | Chacha20Poly1305 P256"
  RUST_LOG=none cargo run -p simple_https_client -- localhost --port 6443 --ciphersuite SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256 2>/dev/null
  print_success

  # kill openssl process
  echo "  Killing the OpenSSL Server"
  kill $pid
}

# === t13 Server <-> OpenSSL Client ===

run_t13() {
  # start t13 server
  cargo run -p simple_https_server -- localhost --port 6443 \
    --ciphersuite $2 \
    --key $cwd/assets/$1_key.der --cert $cwd/assets/$1_cert.der &
  pid=$!

  # give the server time to start up
  sleep 2
}

t13_server_test() {
  echo "Running t13 Server with ECDSA P256 certificate | Chacha20Poly1305 x25519"
  run_t13 p256 SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519
  openssl s_client -curves X25519 -connect localhost:6443 </dev/null
  kill $pid

  echo "Running t13 Server with ECDSA P256 certificate | Chacha20Poly1305 P256"
  run_t13 p256 SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256
  openssl s_client -curves P-256 -connect localhost:6443 </dev/null
  kill $pid

  echo "Running t13 Server with RSA PSS certificate | Chacha20Poly1305 x25519"
  run_t13 rsa SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519
  openssl s_client -curves X25519 -connect localhost:6443 </dev/null
  kill $pid

  echo "Running t13 Server with RSA PSS certificate | Chacha20Poly1305 P256"
  run_t13 rsa SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256
  openssl s_client -curves P-256 -connect localhost:6443 </dev/null
  kill $pid
}

t13_client_test
t13_server_test
