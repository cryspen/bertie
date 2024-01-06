# Bertie

Raw numbers for Bertie and instructions.

```bash
cargo bench
```

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

## Comparison

We compare with [Rustls](https://github.com/rustls/rustls) as it is the most popular
TLS implementation in Rust and claims to be [almost as fast as OpenSSL](https://www.memorysafety.org/blog/rustls-performance/).

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
