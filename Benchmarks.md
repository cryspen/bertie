# Bertie

Raw numbers for Bertie and instructions.

Some benchmarks are behind the `bench` cfg flag, using internal functions.

```bash
CARGO_PROFILE_BENCH_DEBUG=true RUSTFLAGS='--cfg bench' cargo bench
```

Or run individual benchmarks, e.g.

```bash
CARGO_PROFILE_BENCH_DEBUG=true RUSTFLAGS='--cfg bench' cargo bench --bench client
```

## Profiling

Use `perf`, `instruments`, or `samply` for recording performance data.

## M1 Pro

(Note: libcrux does not support AES-GCM on arm yet.)

```
Client
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 353 μs | 2828.1164436220784 /s 
	Application: 23 μs | 676.7389679421062 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 248 μs | 4028.529416879753 /s 
	Application: 22 μs | 686.0561427074053 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 801 μs | 1247.3822996381828 /s 
	Application: 23 μs | 656.9715189707097 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 700 μs | 1426.6392861489624 /s 
	Application: 23 μs | 662.4049756215892 MB/s

Server
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 290 μs | 3447.9281444603002 /s 
	Application: 23 μs | 655.63603619027 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 179 μs | 5570.4559061650025 /s 
	Application: 23 μs | 663.2543345421753 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 30152 μs | 33.16487582007327 /s 
	Application: 26 μs | 581.9549350486149 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 29332 μs | 34.09151970644297 /s 
	Application: 24 μs | 642.3299067242425 MB/s
```

## Intel AVX2 (Dell XPS13)

```
Client
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 327 μs | 3057.340977293168 /s 
	Application: 8 μs | 1777.9662137489759 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 237 μs | 4208.894452093338 /s 
	Application: 8 μs | 1770.4044351548725 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 572 μs | 1746.9959605208192 /s 
	Application: 11 μs | 1418.959349289308 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 482 μs | 2073.951111202577 /s 
	Application: 10 μs | 1436.2282486104205 MB/s
 - TLS_Aes128Gcm_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 315 μs | 3174.048300578514 /s 
	Application: 5 μs | 3028.1741321252935 MB/s
 - TLS_Aes128Gcm_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 226 μs | 4410.986795927165 /s 
	Application: 5 μs | 3032.8846216930156 MB/s
 - TLS_Aes128Gcm_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 558 μs | 1791.0607299260244 /s 
	Application: 7 μs | 2051.4448539456607 MB/s
 - TLS_Aes128Gcm_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 483 μs | 2067.5939595383065 /s 
	Application: 7 μs | 2135.2973604854787 MB/s
 - TLS_Aes256Gcm_SHA384 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 319 μs | 3125.0838694383465 /s 
	Application: 5 μs | 2647.923155490623 MB/s
 - TLS_Aes256Gcm_SHA384 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 232 μs | 4298.543694662268 /s 
	Application: 5 μs | 2689.5912217250807 MB/s
 - TLS_Aes256Gcm_SHA384 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 547 μs | 1827.658636945311 /s 
	Application: 8 μs | 1844.7886344490812 MB/s
 - TLS_Aes256Gcm_SHA384 w/ RsaPssRsaSha256 | X25519:
	Handshake: 464 μs | 2152.925515862429 /s 
	Application: 8 μs | 1885.4609900836215 MB/s

Server
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 255 μs | 3915.9550521353417 /s 
	Application: 8 μs | 1789.1519110776042 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 166 μs | 5996.368023873411 /s 
	Application: 8 μs | 1799.317951976578 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 25039 μs | 39.936335701305616 /s 
	Application: 8 μs | 1749.0407980417012 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 25271 μs | 39.5695875349339 /s 
	Application: 8 μs | 1737.3882845433932 MB/s
 - TLS_Aes128Gcm_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 251 μs | 3974.1469658464907 /s 
	Application: 4 μs | 3715.1660090723763 MB/s
 - TLS_Aes128Gcm_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 169 μs | 5906.747879409583 /s 
	Application: 4 μs | 3682.732099329354 MB/s
 - TLS_Aes128Gcm_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 24672 μs | 40.53054159896623 /s 
	Application: 4 μs | 3284.6773637484303 MB/s
 - TLS_Aes128Gcm_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 24530 μs | 40.76549603693159 /s 
	Application: 4 μs | 3450.0392366062297 MB/s
 - TLS_Aes256Gcm_SHA384 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 255 μs | 3910.970449669381 /s 
	Application: 4 μs | 3302.1023138174332 MB/s
 - TLS_Aes256Gcm_SHA384 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 170 μs | 5867.885152578217 /s 
	Application: 4 μs | 3324.9434812807276 MB/s
 - TLS_Aes256Gcm_SHA384 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 25596 μs | 39.06807119241344 /s 
	Application: 4 μs | 3136.246580236729 MB/s
 - TLS_Aes256Gcm_SHA384 w/ RsaPssRsaSha256 | X25519:
	Handshake: 25740 μs | 38.84923817237172 /s 
	Application: 5 μs | 3085.4385074573815 MB/s
```

### Analysis

The following shows that the performance is dominated by the cryptographic primitives.
The protocol code in Bertie has no measurable impact on the performance.

#### TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1

| Weight | Symbol name                            |
| ------ | -------------------------------------- |
| 25%    | mont_reduction                         |
| 22%    | bn_mul4                                |
| 13%    | sha256_update                          |
| 3.5%   | bn_sqr4                                |
| 3.4%   | chacha20_core			  |
| 2.5%   | qmont_reduction                        |
| 1.7%   | poly1305_padded_128                    |
| 1.5%   | memory operations			  |



#### TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519

| Weight | Symbol name                                               |
| ------ | --------------------------------------------------------- |
| 64%    | Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64 |
| 16%    | Hacl_Bignum_Multiplication_bn_sqr_u64                     |
| 7%     | Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64             |
| 6%     | Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64             |
| 3%     | Hacl_Bignum_bn_add_mod_n_u64                              |
| 1.4%   | memory operations			  		     |

#### Protocol Performance Analysis

To avoid the large overhead of the cryptography, we look at individual steps of
the protocol.
This allows us to see where the protocol implementation itself may be slower than
necessary.

##### Heap allocations

Because we used a style where `Bytes` and `&Bytes` were used everywhere, everything,
even individual bytes, needed to be allocated on the heap.
While this makes the code look nice, it incurs a huge amount of memory operations,
both for allocating and for freeing.

Using pre-allocation when possible, i.e. allocation all required memory at once,
instead of allocating when, for example, concatenating, and using byte slices `&[U8]`
instead of owning references `&Bytes`, significantly sped up the protocol code.

##### Client Hello Generation

This measures the performance of generating a client hello (`tls13formats::client_hello`).

Looking at the traces, most time is spent in `Bytes::concat` and `encode_length_uXX` functions, and the resulting memory management.
To reduce the time needed here, we pre-allocate memory in `encode_length_uXX`
and make `Bytes::concat` owning, such that it does not need to allocate new memory.

##### Parsing Client Hello

Changing the way extensions are checked to perform fewer copies brought down
the time spend in `check_extensions` from 74% to 41% of the client hello parsing time.

##### Parsing Server Hello

Similarly to the improvements when parsing client hellos, parsing server hellos benefits from the same improvements when checking extension.

##### Parsing Server Certificate

Performance of parsing the server certificate can be improved by 50% by avoiding `slice_range` (copying memory into `Bytes`) and using raw slices instead.

## Comparison

We compare with [Rustls](https://github.com/rustls/rustls) as it is the most popular
TLS implementation in Rust and claims to be [almost as fast as OpenSSL](https://www.memorysafety.org/blog/rustls-performance/).

### M1 Pro

#### Client

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 2828        | 3856        |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 4029        | 4064        |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 1247        | 4060        |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 1426        | 4198        |

#### Server

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 3448        | 7941        |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 5570        | 8663        |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 33          | 1260        |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 34          | 1262        |

#### Send Bulk Data

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 686         | 1076        |
| TLS_AESGCM128_SHA256        |             | 5926        |

#### Receive Bulk Data

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 663         | 1012        |
| TLS_AESGCM128_SHA256        |             | 5279        |


### Intel AVX2 (Dell XPS13)

#### Client

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 3057        | 5051        |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 4208        | 5178        |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 1747        | 5070        |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 2074        | 5242	       |

#### Server

|                                          | Bertie hs/s | Rustls hs/s |
| ---------------------------------------- | ----------- | ----------- |
| P-256 EcDSA TLS_Chacha20Poly1305_SHA256  | 3916        | 10946       |
| X25519 EcDSA TLS_Chacha20Poly1305_SHA256 | 5996        | 9474        |
| P-256 RSA TLS_Chacha20Poly1305_SHA256    | 40          | 1810        |
| X25519 RSA TLS_Chacha20Poly1305_SHA256   | 40          | 1760        |

#### Send Bulk Data

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 1789        | 2253        |
| TLS_AESGCM128_SHA256        | 3715        | 5776        |

#### Receive Bulk Data

|                             | Bertie MB/s | Rustls MB/s |
| --------------------------- | ----------- | ----------- |
| TLS_Chacha20Poly1305_SHA256 | 1770        | 2168        |
| TLS_AESGCM128_SHA256        | 3028        | 5255        |

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
