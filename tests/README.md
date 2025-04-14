# t13 Tests

Most tests can be run with `cargo test`.

## Interop tests

t13 implements a number of interop tests.

### BoGo

Bogo is a TLS test framework from BoringSSL.
Please see the [Bogo Readme] for more details.

### OpenSSL

The [openssl-interop.sh] script can be used to run t13 against OpenSSL.

[bogo readme]: ../bogo_shim/README.md
[openssl-interop.sh]: ./openssl-interop.sh
