# Bertie Tests

Most tests can be run with `cargo test`.

## Interop tests

Bertie implements a number of interop tests.

### BoGo

Bogo is a TLS test framework from BoringSSL.
Please see the [Bogo Readme] for more details.

### OpenSSL

The [openssl-interop.sh] script can be used to run Bertie against OpenSSL.

[bogo readme]: ../bogo_shim/README.md
[openssl-interop.sh]: ./openssl-interop.sh
