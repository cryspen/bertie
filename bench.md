# Raspberry Pi 3
```
       _,met$$$$$gg.          jonas@raspberrypi
    ,g$$$$$$$$$$$$$$$P.       -----------------
  ,g$$P"     """Y$$.".        OS: Debian GNU/Linux 11 (bullseye) aarch64
 ,$$P'              `$$$.     Host: Raspberry Pi 3 Model B Rev 1.2
',$$P       ,ggs.     `$$b:   Kernel: 6.1.21-v8+
`d$$'     ,$P"'   .    $$$    Uptime: 2 hours, 41 mins
 $$P      d$'     ,    $$P    Packages: 660 (dpkg)
 $$:      $$.   -    ,d$$'    Shell: bash 5.1.4
 $$;      Y$b._   _,d$P'      Terminal: /dev/pts/0
 Y$$.    `.`"Y$$$$P"'         CPU: BCM2835 (4) @ 1.200GHz
 `$$b      "-.__              Memory: 82MiB / 909MiB
  `Y$$
   `Y$$.
     `$$b.
       `Y$$b.
          `"Y$b._
              `"""
```

## Client
Client
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 7122 μs | 140.4094748062547 /s
	Application: 244 μs | 63.7759811051013 MB/s
	Message Sizes: 200, 838, 58 bytes
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 4566 μs | 218.98451159470278 /s
	Application: 245 μs | 63.71299735155773 MB/s
	Message Sizes: 167, 805, 58 bytes
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 21473 μs | 46.56802728954948 /s
	Application: 254 μs | 61.3644019146746 MB/s
	Message Sizes: 200, 2230, 58 bytes
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 18850 μs | 53.05039006817865 /s
	Application: 254 μs | 61.42504065826636 MB/s
	Message Sizes: 167, 2197, 58 bytes
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519Kyber768Draft00:
	Handshake: 5582 μs | 179.1359595215902 /s
	Application: 256 μs | 61.01392340465518 MB/s
	Message Sizes: 1351, 1893, 58 bytes
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519MlKem768:
	Handshake: 5487 μs | 182.24313662925482 /s
	Application: 253 μs | 61.53509645857742 MB/s
	Message Sizes: 1351, 1892, 58 bytes
    
## Client Stack
Client Stack Usage:
===================

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1
[Client Connect] Highest stack usage: 56.1 KB
[Client Read   ] Highest stack usage: 5.9 KB

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519
[Client Connect] Highest stack usage: 55.4 KB
[Client Read   ] Highest stack usage: 5.9 KB

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1
[Client Connect] Highest stack usage: 56.1 KB
[Client Read   ] Highest stack usage: 5.9 KB

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519
[Client Connect] Highest stack usage: 55.4 KB
[Client Read   ] Highest stack usage: 5.9 KB

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519Kyber768Draft00
[Client Connect] Highest stack usage: 78.2 KB
[Client Read   ] Highest stack usage: 5.9 KB

Ciphersuite: TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519MlKem768
[Client Connect] Highest stack usage: 78.2 KB
[Client Read   ] Highest stack usage: 5.9 KB

## Server
Server
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | Secp256r1:
	Handshake: 5481 μs | 182.43040791837637 /s
	Application: 259 μs | 60.18269424576024 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ EcdsaSecp256r1Sha256 | X25519:
	Handshake: 2819 μs | 354.63931635299485 /s
	Application: 256 μs | 60.92005874557329 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | Secp256r1:
	Handshake: 699193 μs | 1.430219917317012 /s
	Application: 262 μs | 59.581248116755916 MB/s
 - TLS_Chacha20Poly1305_SHA256 w/ RsaPssRsaSha256 | X25519:
	Handshake: 694248 μs | 1.4404070652725713 /s
	Application: 260 μs | 60.00107706253405 MB/s
