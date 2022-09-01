# BoGo Shim for Bertie

This application is expected to be called by the [BoGo test runner].

## Usage

Compile this crate with ...

```shell
cargo build
```

... and point the Bogo test runner via its `-shim-path` to the compiled `/target/debug/bogo_shim`.
See [BoGo Integration Architecture] for more information.

(We will provide a more detailed description of how to run the BoGo test suite with Bertie later.)

[BoGo test runner]: https://github.com/google/boringssl/blob/master/ssl/test/PORTING.md#integration-architecture
[BoGo Integration Architecture]: https://github.com/google/boringssl/blob/master/ssl/test/PORTING.md#integration-architecture