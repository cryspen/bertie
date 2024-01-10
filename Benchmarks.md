# Bertie

Raw numbers for Bertie and instructions.

Some benchmarks are behind the `bench` cfg flag, using internal functions.

```bash
CARGO_PROFILE_BENCH_DEBUG=true RUSTFLAGS='--cfg bench' cargo bench --bench client --no-default-features
```

Or run individual benchmarks, e.g.

```bash
CARGO_PROFILE_BENCH_DEBUG=true RUSTFLAGS='--cfg bench' cargo bench --bench client --no-default-features
```

## Profiling

Use `perf`, `instruments`, or `samply` for recording performance data.

## M1 Pro

```
Client
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
        Handshake: 1124 μs | 889.5279890515473 /s
        Application: 57 μs | 271.88892941363173 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
        Handshake: 662 μs | 1508.360146446083 /s
        Application: 52 μs | 295.2477303244078 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
        Handshake: 3325 μs | 300.72603444463067 /s
        Application: 55 μs | 282.3881598304334 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
        Handshake: 2858 μs | 349.87798320226005 /s
        Application: 55 μs | 280.6845217351315 MB/s

Server
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
        Handshake: 848 μs | 1178.1233150627613 /s
        Application: 50 μs | 309.3497063306116 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
        Handshake: 373 μs | 2676.785056943784 /s
        Application: 50 μs | 311.51325062731297 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
        Handshake: 62523 μs | 15.994086881158827 /s
        Application: 53 μs | 291.4021356932462 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
        Handshake: 62086 μs | 16.106602504765714 /s
        Application: 52 μs | 295.57390142038156 MB/s
```

### Analysis

The following shows that the performance is dominated by the cryptographic primitives.
The protocol code in Bertie has no measurable impact on the performance.

#### TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1

| Weight | Self weight | Symbol name                            |
| ------ | ----------- | -------------------------------------- |
| 20.8%  | 4.81 Gc     | FStar_UInt64_gte_mask                  |
| 14.1%  | 3.27 Gc     | FStar_UInt64_eq_mask                   |
| 14.1%  | 3.25 Gc     | bn_mul4                                |
| 12.5%  | 2.88 Gc     | mont_reduction                         |
| 10.1%  | 2.33 Gc     | bn_add_mod4                            |
| 5.4%   | 1.27 Gc     | sha256_update                          |
| 4.0%   | 934.49 Mc   | fsub0                                  |
| 3.3%   | 768.91 Mc   | chacha20_encrypt_block                 |
| 3.2%   | 754.40 Mc   | Hacl_Bignum_Addition_bn_add_eq_len_u64 |
| 1.5%   | 361.09 Mc   | poly1305_padded_32                     |
| 0.8%   | 203.45 Mc   | bn_sqr4                                |

#### TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519

| Weight | Self weight | Symbol name                                               |
| ------ | ----------- | --------------------------------------------------------- |
| 38.6%  | 27.83 Gc    | Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64 |
| 15.3%  | 11.03 Gc    | FStar_UInt64_gte_mask                                     |
| 13.2%  | 9.50 Gc     | FStar_UInt64_eq_mask                                      |
| 9.7%   | 7.04 Gc     | Hacl_Bignum_Addition_bn_add_eq_len_u64                    |
| 8.4%   | 6.05 Gc     | Hacl_Bignum_Multiplication_bn_sqr_u64                     |
| 4.7%   | 3.40 Gc     | Hacl_Bignum_Addition_bn_sub_eq_len_u64                    |
| 3.5%   | 2.52 Gc     | Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64             |
| 2.7%   | 1.97 Gc     | Hacl_Bignum_bn_add_mod_n_u64                              |
| 0.9%   | 702.17 Mc   | Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64             |

#### Protocol Performance Analysis

To avoid the large overhead of the cryptography, we look at individual steps of
the protocol.
This allows us to see where the protocol implementation itself may be slower than
necessary.

##### Client Hello Generation

This measures the performance of generating a client hello (`tls13formats::client_hello`).

Looking at the traces, most time is spent in `Bytes::concat` and `encode_length_uXX` functions, and the resulting memory management.
To reduce the time needed here, we pre-allocate memory in `encode_length_uXX`
and make `Bytes::concat` owning, such that it does not need to allocate new memory.

## Comparison

We compare with [Rustls](https://github.com/rustls/rustls) as it is the most popular
TLS implementation in Rust and claims to be [almost as fast as OpenSSL](https://www.memorysafety.org/blog/rustls-performance/).

- [ ] Note that simd is currently disabled on arm in libcrux.

### M1 Pro

#### Client

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 889.52      | 3856.48     |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 1508.36     | 4064.29     |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 300.72      | 4059.82     |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 349.87      | 4197.59     |

#### Server

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 1178.12     | 7941.33     |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 2676.78     | 8662.90     |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 15.99       | 1260.10     |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 16.10       | 1261.51     |

#### Send (client)

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 271.88      | 1075.67     |
| TLS_AESGCM128_SHA256        |             |             |

#### Receive (server)

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 309.34      | 1011.69     |
| TLS_AESGCM128_SHA256        |             |             |

# Rustls

Raw numbers for Rustls and instructions.

Get rustls and run benchmarks

```bash
git clone git@github.com:rustls/rustls.git
cd rustls
cargo run -p rustls --release --example bench
```

Note that by default ChachaPoly is only benchmarked with RSA.
The EcDSA variant can be added in `bench_impl.rs`.

Further, it does not seem possible to select the key exchange algorithm.
The crypto providers in Rustls define an order of `x25519, P256, P384`, such that
only `x25519` is used by default.
