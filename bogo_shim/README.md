# BoGo Shim for t13

This application is expected to be called by the [BoGo test runner].

## Usage

Compile this crate with ...

```shell
cargo build
```

... and point the Bogo test runner via its `-shim-path` to the compiled `/target/debug/bogo_shim`.
See [BoGo Integration Architecture] for more information.

Check out [BoringSSL], go to `boringssl/ssl/test/runner`, and run

```
go test \
  -shim-path $t13_PATH/target/debug/bogo_shim \
  -shim-config $t13_PATH/bogo_shim/assets/config.json \
  -allow-unimplemented
```

where `t13_PATH` is set to the t13 directory.

(We will provide a more detailed description of how to run the BoGo test suite with t13 later.)

[bogo test runner]: https://github.com/google/boringssl/blob/master/ssl/test/PORTING.md#integration-architecture
[bogo integration architecture]: https://github.com/google/boringssl/blob/master/ssl/test/PORTING.md#integration-architecture
[boringssl]: https://github.com/google/boringssl
