use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use bertie::*;
#[cfg(not(feature = "evercrypt"))]
use hacspec_cryptolib::*;
#[cfg(feature = "evercrypt")]
use evercrypt_cryptolib::*;

// These are the sample TLS 1.3 traces taken from RFC 8448

fn load_hex(s: &str) -> Bytes {
    let s_no_ws: String = s.split_whitespace().collect();
    Bytes::from_hex(&s_no_ws)
}

/* Server's RSA Private Key */
const modulus: &str = "b4 bb 49 8f 82 79 30 3d 98 08 36 39 9b 36 c6 98 8c
0c 68 de 55 e1 bd b8 26 d3 90 1a 24 61 ea fd 2d e4 9a 91 d0 15 ab
bc 9a 95 13 7a ce 6c 1a f1 9e aa 6a f9 8c 7c ed 43 12 09 98 e1 87
a8 0e e0 cc b0 52 4b 1b 01 8c 3e 0b 63 26 4d 44 9a 6d 38 e2 2a 5f
da 43 08 46 74 80 30 53 0e f0 46 1c 8c a9 d9 ef bf ae 8e a6 d1 d0
3e 2b d1 93 ef f0 ab 9a 80 02 c4 74 28 a6 d3 5a 8d 88 d7 9f 7f 1e
3f";

const public_exponent: &str = "01 00 01";

const private_exponent: &str = "04 de a7 05 d4 3a 6e a7 20 9d d8 07 21 11 a8 3c 81
e3 22 a5 92 78 b3 34 80 64 1e af 7c 0a 69 85 b8 e3 1c 44 f6 de 62
e1 b4 c2 30 9f 61 26 e7 7b 7c 41 e9 23 31 4b bf a3 88 13 05 dc 12
17 f1 6c 81 9c e5 38 e9 22 f3 69 82 8d 0e 57 19 5d 8c 84 88 46 02
07 b2 fa a7 26 bc f7 08 bb d7 db 7f 67 9f 89 34 92 fc 2a 62 2e 08
97 0a ac 44 1c e4 e0 c3 08 8d f2 5a e6 79 23 3d f8 a3 bd a2 ff 99
41";

const prime1: &str = "e4 35 fb 7c c8 37 37 75 6d ac ea 96 ab 7f 59 a2 cc 10 69 db
7d eb 19 0e 17 e3 3a 53 2b 27 3f 30 a3 27 aa 0a aa bc 58 cd 67 46
6a f9 84 5f ad c6 75 fe 09 4a f9 2c 4b d1 f2 c1 bc 33 dd 2e 05 15";

const prime2: &str = "ca bd 3b c0 e0 43 86 64 c8 d4 cc 9f 99 97 7a 94 d9 bb fe ad
8e 43 87 0a ba e3 f7 eb 8b 4e 0e ee 8a f1 d9 b4 71 9b a6 19 6c f2
cb ba ee eb f8 b3 49 0a fe 9e 9f fa 74 a8 8a a5 1f c6 45 62 93 03";

const exponent1: &str = "3f 57 34 5c 27 fe 1b 68 7e 6e 76 16 27 b7 8b 1b 82 64 33
dd 76 0f a0 be a6 a6 ac f3 94 90 aa 1b 47 cd a4 86 9d 68 f5 84 dd
5b 50 29 bd 32 09 3b 82 58 66 1f e7 15 02 5e 5d 70 a4 5a 08 d3 d3
19";

const exponent2: &str = "18 3d a0 13 63 bd 2f 28 85 ca cb dc 99 64 bf 47 64 f1 51
76 36 f8 64 01 28 6f 71 89 3c 52 cc fe 40 a6 c2 3d 0d 08 6b 47 c6
fb 10 d8 fd 10 41 e0 4d ef 7e 9a 40 ce 95 7c 41 77 94 e1 04 12 d1
39";

const coefficient: &str = "83 9c a9 a0 85 e4 28 6b 2c 90 e4 66 99 7a 2c 68 1f 21
33 9a a3 47 78 14 e4 de c1 18 33 05 0e d5 0d d1 3c c0 38 04 8a 43
c5 9b 2a cc 41 68 89 c0 37 66 5f e5 af a6 05 96 9f 8c 01 df a5 ca
96 9d";

// ECDH keys

const client_x25519_priv: &str = "49 af 42 ba 7f 79 94 85 2d 71 3e f2 78
4b cb ca a7 91 1d e2 6a dc 56 42 cb 63 45 40 e7 ea 50 05";

const client_x25519_pub: &str = "99 38 1d e5 60 e4 bd 43 d2 3d 8e 43 5a 7d
ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a af 2c";

const server_x25519_priv: &str = "b1 58 0e ea df 6d d5 89 b8 ef 4f 2d 56
52 57 8c c8 10 e9 98 01 91 ec 8d 05 83 08 ce a2 16 a2 1e";

const server_x25519_pub: &str = "c9 82 88 76 11 20 95 fe 66 76 2b db f7 c6
72 e1 56 d6 cc 25 3b 83 3d f1 dd 69 b1 b0 4e 75 1f 0f";

const shared_secret: &str = "8b d4 05 4f b5 5b 9d 63 fd fb ac f9 f0 4b 9f 0d
35 e6 d6 3f 53 75 63 ef d4 62 72 90 0f 89 49 2d";

//Simple 1-RTT Handshake Transcript

const client_hello: &str = "01 00 00 c0 03 03 cb 34 ec b1 e7 81 63
ba 1c 38 c6 da cb 19 6a 6d ff a2 1a 8d 99 12 ec 18 a2 ef 62 83
02 4d ec e7 00 00 06 13 01 13 03 13 02 01 00 00 91 00 00 00 0b
00 09 00 00 06 73 65 72 76 65 72 ff 01 00 01 00 00 0a 00 14 00
12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02 01 03 01 04 00 23
00 00 00 33 00 26 00 24 00 1d 00 20 99 38 1d e5 60 e4 bd 43 d2
3d 8e 43 5a 7d ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a
af 2c 00 2b 00 03 02 03 04 00 0d 00 20 00 1e 04 03 05 03 06 03
02 03 08 04 08 05 08 06 04 01 05 01 06 01 02 01 04 02 05 02 06
02 02 02 00 2d 00 02 01 01 00 1c 00 02 40 01";

const client_hello_record: &str = "16 03 01 00 c4 01 00 00 c0 03 03 cb
34 ec b1 e7 81 63 ba 1c 38 c6 da cb 19 6a 6d ff a2 1a 8d 99 12
ec 18 a2 ef 62 83 02 4d ec e7 00 00 06 13 01 13 03 13 02 01 00
00 91 00 00 00 0b 00 09 00 00 06 73 65 72 76 65 72 ff 01 00 01
00 00 0a 00 14 00 12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02
01 03 01 04 00 23 00 00 00 33 00 26 00 24 00 1d 00 20 99 38 1d
e5 60 e4 bd 43 d2 3d 8e 43 5a 7d ba fe b3 c0 6e 51 c1 3c ae 4d
54 13 69 1e 52 9a af 2c 00 2b 00 03 02 03 04 00 0d 00 20 00 1e
04 03 05 03 06 03 02 03 08 04 08 05 08 06 04 01 05 01 06 01 02
01 04 02 05 02 06 02 02 02 00 2d 00 02 01 01 00 1c 00 02 40 01";

const server_hello: &str = "02 00 00 56 03 03 a6 af 06 a4 12 18 60
dc 5e 6e 60 24 9c d3 4c 95 93 0c 8a c5 cb 14 34 da c1 55 77 2e
d3 e2 69 28 00 13 01 00 00 2e 00 33 00 24 00 1d 00 20 c9 82 88
76 11 20 95 fe 66 76 2b db f7 c6 72 e1 56 d6 cc 25 3b 83 3d f1
dd 69 b1 b0 4e 75 1f 0f 00 2b 00 02 03 04";

const server_hello_record: &str = "16 03 03 00 5a 02 00 00 56 03 03 a6
af 06 a4 12 18 60 dc 5e 6e 60 24 9c d3 4c 95 93 0c 8a c5 cb 14
34 da c1 55 77 2e d3 e2 69 28 00 13 01 00 00 2e 00 33 00 24 00
1d 00 20 c9 82 88 76 11 20 95 fe 66 76 2b db f7 c6 72 e1 56 d6
cc 25 3b 83 3d f1 dd 69 b1 b0 4e 75 1f 0f 00 2b 00 02 03 04";

const encrypted_extensions: &str = "08 00 00 24 00 22 00 0a 00 14 00
12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02 01 03 01 04 00 1c
00 02 40 01 00 00 00 00";

const server_certificate: &str = "0b 00 01 b9 00 00 01 b5 00 01 b0 30 82
01 ac 30 82 01 15 a0 03 02 01 02 02 01 02 30 0d 06 09 2a 86 48
86 f7 0d 01 01 0b 05 00 30 0e 31 0c 30 0a 06 03 55 04 03 13 03
72 73 61 30 1e 17 0d 31 36 30 37 33 30 30 31 32 33 35 39 5a 17
0d 32 36 30 37 33 30 30 31 32 33 35 39 5a 30 0e 31 0c 30 0a 06
03 55 04 03 13 03 72 73 61 30 81 9f 30 0d 06 09 2a 86 48 86 f7
0d 01 01 01 05 00 03 81 8d 00 30 81 89 02 81 81 00 b4 bb 49 8f
82 79 30 3d 98 08 36 39 9b 36 c6 98 8c 0c 68 de 55 e1 bd b8 26
d3 90 1a 24 61 ea fd 2d e4 9a 91 d0 15 ab bc 9a 95 13 7a ce 6c
1a f1 9e aa 6a f9 8c 7c ed 43 12 09 98 e1 87 a8 0e e0 cc b0 52
4b 1b 01 8c 3e 0b 63 26 4d 44 9a 6d 38 e2 2a 5f da 43 08 46 74
80 30 53 0e f0 46 1c 8c a9 d9 ef bf ae 8e a6 d1 d0 3e 2b d1 93
ef f0 ab 9a 80 02 c4 74 28 a6 d3 5a 8d 88 d7 9f 7f 1e 3f 02 03
01 00 01 a3 1a 30 18 30 09 06 03 55 1d 13 04 02 30 00 30 0b 06
03 55 1d 0f 04 04 03 02 05 a0 30 0d 06 09 2a 86 48 86 f7 0d 01
01 0b 05 00 03 81 81 00 85 aa d2 a0 e5 b9 27 6b 90 8c 65 f7 3a
72 67 17 06 18 a5 4c 5f 8a 7b 33 7d 2d f7 a5 94 36 54 17 f2 ea
e8 f8 a5 8c 8f 81 72 f9 31 9c f3 6b 7f d6 c5 5b 80 f2 1a 03 01
51 56 72 60 96 fd 33 5e 5e 67 f2 db f1 02 70 2e 60 8c ca e6 be
c1 fc 63 a4 2a 99 be 5c 3e b7 10 7c 3c 54 e9 b9 eb 2b d5 20 3b
1c 3b 84 e0 a8 b2 f7 59 40 9b a3 ea c9 d9 1d 40 2d cc 0c c8 f8
96 12 29 ac 91 87 b4 2b 4d e1 00 00";

const server_certificate_verify: &str = "0f 00 00 84 08 04 00 80 5a 74 7c
5d 88 fa 9b d2 e5 5a b0 85 a6 10 15 b7 21 1f 82 4c d4 84 14 5a
b3 ff 52 f1 fd a8 47 7b 0b 7a bc 90 db 78 e2 d3 3a 5c 14 1a 07
86 53 fa 6b ef 78 0c 5e a2 48 ee aa a7 85 c4 f3 94 ca b6 d3 0b
be 8d 48 59 ee 51 1f 60 29 57 b1 54 11 ac 02 76 71 45 9e 46 44
5c 9e a5 8c 18 1e 81 8e 95 b8 c3 fb 0b f3 27 84 09 d3 be 15 2a
3d a5 04 3e 06 3d da 65 cd f5 ae a2 0d 53 df ac d4 2f 74 f3";

const server_finished: &str = "14 00 00 20 9b 9b 14 1d 90 63 37 fb d2 cb
dc e7 1d f4 de da 4a b4 2c 30 95 72 cb 7f ff ee 54 54 b7 8f 07
18";

const server_finished_record: &str = "17 03 03 02 a2 d1 ff 33 4a 56 f5 bf
f6 59 4a 07 cc 87 b5 80 23 3f 50 0f 45 e4 89 e7 f3 3a f3 5e df
78 69 fc f4 0a a4 0a a2 b8 ea 73 f8 48 a7 ca 07 61 2e f9 f9 45
cb 96 0b 40 68 90 51 23 ea 78 b1 11 b4 29 ba 91 91 cd 05 d2 a3
89 28 0f 52 61 34 aa dc 7f c7 8c 4b 72 9d f8 28 b5 ec f7 b1 3b
d9 ae fb 0e 57 f2 71 58 5b 8e a9 bb 35 5c 7c 79 02 07 16 cf b9
b1 18 3e f3 ab 20 e3 7d 57 a6 b9 d7 47 76 09 ae e6 e1 22 a4 cf
51 42 73 25 25 0c 7d 0e 50 92 89 44 4c 9b 3a 64 8f 1d 71 03 5d
2e d6 5b 0e 3c dd 0c ba e8 bf 2d 0b 22 78 12 cb b3 60 98 72 55
cc 74 41 10 c4 53 ba a4 fc d6 10 92 8d 80 98 10 e4 b7 ed 1a 8f
d9 91 f0 6a a6 24 82 04 79 7e 36 a6 a7 3b 70 a2 55 9c 09 ea d6
86 94 5b a2 46 ab 66 e5 ed d8 04 4b 4c 6d e3 fc f2 a8 94 41 ac
66 27 2f d8 fb 33 0e f8 19 05 79 b3 68 45 96 c9 60 bd 59 6e ea
52 0a 56 a8 d6 50 f5 63 aa d2 74 09 96 0d ca 63 d3 e6 88 61 1e
a5 e2 2f 44 15 cf 95 38 d5 1a 20 0c 27 03 42 72 96 8a 26 4e d6
54 0c 84 83 8d 89 f7 2c 24 46 1a ad 6d 26 f5 9e ca ba 9a cb bb
31 7b 66 d9 02 f4 f2 92 a3 6a c1 b6 39 c6 37 ce 34 31 17 b6 59
62 22 45 31 7b 49 ee da 0c 62 58 f1 00 d7 d9 61 ff b1 38 64 7e
92 ea 33 0f ae ea 6d fa 31 c7 a8 4d c3 bd 7e 1b 7a 6c 71 78 af
36 87 90 18 e3 f2 52 10 7f 24 3d 24 3d c7 33 9d 56 84 c8 b0 37
8b f3 02 44 da 8c 87 c8 43 f5 e5 6e b4 c5 e8 28 0a 2b 48 05 2c
f9 3b 16 49 9a 66 db 7c ca 71 e4 59 94 26 f7 d4 61 e6 6f 99 88
2b d8 9f c5 08 00 be cc a6 2d 6c 74 11 6d bd 29 72 fd a1 fa 80
f8 5d f8 81 ed be 5a 37 66 89 36 b3 35 58 3b 59 91 86 dc 5c 69
18 a3 96 fa 48 a1 81 d6 b6 fa 4f 9d 62 d5 13 af bb 99 2f 2b 99
2f 67 f8 af e6 7f 76 91 3f a3 88 cb 56 30 c8 ca 01 e0 c6 5d 11
c6 6a 1e 2a c4 c8 59 77 b7 c7 a6 99 9b bf 10 dc 35 ae 69 f5 51
56 14 63 6c 0b 9b 68 c1 9e d2 e3 1c 0b 3b 66 76 30 38 eb ba 42
f3 b3 8e dc 03 99 f3 a9 f2 3f aa 63 97 8c 31 7f c9 fa 66 a7 3f
60 f0 50 4d e9 3b 5b 84 5e 27 55 92 c1 23 35 ee 34 0b bc 4f dd
d5 02 78 40 16 e4 b3 be 7e f0 4d da 49 f4 b4 40 a3 0c b5 d2 af
93 98 28 fd 4a e3 79 4e 44 f9 4d f5 a6 31 ed e4 2c 17 19 bf da
bf 02 53 fe 51 75 be 89 8e 75 0e dc 53 37 0d 2b";

const client_finished: &str = "14 00 00 20 a8 ec 43 6d 67 76 34 ae 52 5a
c1 fc eb e1 1a 03 9e c1 76 94 fa c6 e9 85 27 b6 42 f2 ed d5 ce
61";

const client_finished_record: &str = "17 03 03 00 35 75 ec 4d c2 38 cc e6
0b 29 80 44 a7 1e 21 9c 56 cc 77 b0 51 7f e9 b9 3c 7a 4b fc 44
d8 7f 38 f8 03 38 ac 98 fc 46 de b3 84 bd 1c ae ac ab 68 67 d7
26 c4 05 46";

const TLS_AES_128_GCM_SHA256_X25519_RSA: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::RsaPssRsaSha256,
    NamedGroup::X25519,
    false,
    false,
);

const TLS_AES_128_GCM_SHA256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Aes128Gcm,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);
const TLS_CHACHA20_POLY1305_SHA256_X25519: Algorithms = Algorithms(
    HashAlgorithm::SHA256,
    AeadAlgorithm::Chacha20Poly1305,
    SignatureScheme::EcdsaSecp256r1Sha256,
    NamedGroup::X25519,
    false,
    false,
);

const ECDSA_P256_SHA256_CERT: [u8; 522] = [
    0x30, 0x82, 0x02, 0x06, 0x30, 0x82, 0x01, 0xAC, 0x02, 0x09, 0x00, 0xD1, 0xA2, 0xE4, 0xD5, 0x78,
    0x05, 0x08, 0x61, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02, 0x30,
    0x81, 0x8A, 0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31,
    0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69,
    0x6E, 0x31, 0x10, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73,
    0x70, 0x65, 0x63, 0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62,
    0x65, 0x72, 0x74, 0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30,
    0x1B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x1E, 0x17, 0x0D,
    0x32, 0x31, 0x30, 0x34, 0x32, 0x39, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x17, 0x0D, 0x33,
    0x31, 0x30, 0x34, 0x32, 0x37, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x30, 0x81, 0x8A, 0x31,
    0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31, 0x0F, 0x30, 0x0D,
    0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x0F, 0x30,
    0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x10,
    0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62, 0x65, 0x72, 0x74,
    0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30, 0x1B, 0x06, 0x09,
    0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2A,
    0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07,
    0x03, 0x42, 0x00, 0x04, 0xD8, 0xE0, 0x74, 0xF7, 0xCB, 0xEF, 0x19, 0xC7, 0x56, 0xA4, 0x52, 0x59,
    0x0C, 0x02, 0x70, 0xCC, 0x9B, 0xFC, 0x45, 0x8D, 0x73, 0x28, 0x39, 0x1D, 0x3B, 0xF5, 0x26, 0x17,
    0x8B, 0x0D, 0x25, 0x04, 0x91, 0xE8, 0xC8, 0x72, 0x22, 0x59, 0x9A, 0x2C, 0xBB, 0x26, 0x31, 0xB1,
    0xCC, 0x6B, 0x6F, 0x5A, 0x10, 0xD9, 0x7D, 0xD7, 0x86, 0x56, 0xFB, 0x89, 0x39, 0x9E, 0x0A, 0x91,
    0x9F, 0x35, 0x81, 0xE7, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02,
    0x03, 0x48, 0x00, 0x30, 0x45, 0x02, 0x21, 0x00, 0xA1, 0x81, 0xB3, 0xD6, 0x8C, 0x9F, 0x62, 0x66,
    0xC6, 0xB7, 0x3F, 0x26, 0xE7, 0xFD, 0x88, 0xF9, 0x4B, 0xD8, 0x15, 0xD1, 0x45, 0xC7, 0x66, 0x69,
    0x40, 0xC2, 0x55, 0x21, 0x84, 0x9F, 0xE6, 0x8C, 0x02, 0x20, 0x10, 0x7E, 0xEF, 0xF3, 0x1D, 0x58,
    0x32, 0x6E, 0xF7, 0xCB, 0x0A, 0x47, 0xF2, 0xBA, 0xEB, 0xBC, 0xB7, 0x8F, 0x46, 0x56, 0xF1, 0x5B,
    0xCC, 0x2E, 0xD5, 0xB3, 0xC4, 0x0F, 0x5B, 0x22, 0xBD, 0x02,
];
const ECDSA_P256_SHA256_Key: [u8; 32] = [
    0xA6, 0xDE, 0x48, 0x21, 0x0E, 0x56, 0x12, 0xDD, 0x95, 0x3A, 0x91, 0x4E, 0x9F, 0x56, 0xC3, 0xA2,
    0xDB, 0x7A, 0x36, 0x20, 0x08, 0xE9, 0x52, 0xEE, 0xDB, 0xCE, 0xAC, 0x3B, 0x26, 0xF9, 0x20, 0xBD,
];

#[test]
fn test_parse_client_hello() {
    let ch = handshake_data(load_hex(client_hello));
    //   let default_algs = Algorithms(SHA256,CHACHA20_POLY1305,ECDSA_SECP256R1_SHA256,X25519,false,false);
    let res = parse_client_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &ch);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok((cr, sid, sn, gx, tkto, bo, l)) => {
            println!("Parsed CH!");
            println!("cr: {}", cr.to_hex());
            println!("sid: {}", sid.to_hex());
            println!("sn: {}", sn.to_hex());
            println!("gx: {}", gx.to_hex());
            println!("trunc_len: {}", l);
        }
    }
    assert!(b);
}

#[test]
fn test_parse_client_hello_record() {
    let mut ch: Bytes = load_hex(client_hello_record);
    ch[2] = U8(3);
    //   let default_algs = Algorithms(SHA256,CHACHA20_POLY1305,ECDSA_SECP256R1_SHA256,X25519,false,false);
    let mut b = true;
    match check_handshake_record(&ch) {
        Err(x) => {
            println!("Error: {}", x);
            b = false;
        }
        Ok((hs, len)) => match parse_client_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &hs) {
            Err(x) => {
                println!("Error: {}", x);
                b = false;
            }
            Ok((cr, sid, sn, gx, tkto, bo, l)) => {
                println!("Parsed CH!");
                println!("cr: {}", cr.to_hex());
                println!("sid: {}", sid.to_hex());
                println!("sn: {}", sn.to_hex());
                println!("gx: {}", gx.to_hex());
                println!("trunc_len: {}", l);
            }
        },
    }
    assert!(b);
}

#[test]
fn test_parse_client_hello_roundtrip() {
    let cr: Random = Random::new();
    let gx = load_hex(client_x25519_pub);
    let sn = Bytes::new(23);
    let ch = tls13formats::client_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &cr, &gx, &sn, &None);
    let mut b = true;
    match ch {
        Err(x) => {
            println!("Error serializing: {}", x);
            b = false;
        }
        Ok((ch, _)) => {
            //   let default_algs = Algorithms(SHA256,CHACHA20_POLY1305,ECDSA_SECP256R1_SHA256,X25519,false,false);
            let res = parse_client_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &ch);
            let b = res.is_ok();
            match res {
                Err(x) => {
                    println!("Error: {}", x);
                }
                Ok((cr, sid, sn, gx, tkto, bo, l)) => {
                    println!("Parsed CH!");
                    println!("cr: {}", cr.to_hex());
                    println!("sid: {}", sid.to_hex());
                    println!("sn: {}", sn.to_hex());
                    println!("gx: {}", gx.to_hex());
                    println!("trunc_len: {}", l);
                }
            }
        }
    }
    assert!(b);
}

#[test]
fn test_parse_server_hello() {
    let sh = handshake_data(load_hex(server_hello));
    //   let default_algs = Algorithms(SHA256,AES_128_GCM,ECDSA_SECP256R1_SHA256,X25519,false,false);
    let res = parse_server_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &sh);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok((sr, gy)) => {
            println!("Parsed SH!");
            println!("sr: {}", sr.to_hex());
            println!("gy: {}", gy.to_hex());
        }
    }
    assert!(b);
}

#[test]
fn test_parse_server_hello_roundtrip() {
    let sr: Random = Random::new();
    let mut sid = Bytes::new(24);
    sid[0] = U8(255);
    let gy = load_hex(server_x25519_pub);
    let sh = tls13formats::server_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &sr, &sid, &gy);
    let mut b = true;
    match sh {
        Err(x) => {
            println!("Error serializing: {}", x);
            b = false;
        }
        Ok(sh) => {
            //   let default_algs = Algorithms(SHA256,CHACHA20_POLY1305,ECDSA_SECP256R1_SHA256,X25519,false,false);
            let res = parse_server_hello(&TLS_AES_128_GCM_SHA256_X25519_RSA, &sh);
            let b = res.is_ok();
            match res {
                Err(x) => {
                    println!("Error: {}", x);
                }
                Ok((sr, gy)) => {
                    println!("Parsed SH!");
                    println!("sr: {}", sr.to_hex());
                    println!("gy: {}", gy.to_hex());
                }
            }
        }
    }
    assert!(b);
}

#[test]
fn test_parse_encrypted_extensions() {
    let ee = handshake_data(load_hex(encrypted_extensions));
    let res = parse_encrypted_extensions(&TLS_AES_128_GCM_SHA256_X25519_RSA, &ee);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(()) => {
            println!("Parsed EE!");
        }
    }
    assert!(b);
}

#[test]
fn test_parse_server_certificate() {
    let sc = handshake_data(load_hex(server_certificate));
    let res = parse_server_certificate(&TLS_AES_128_GCM_SHA256_X25519_RSA, &sc);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(_) => {
            println!("Parsed SC!");
        }
    }
    assert!(b);
}

#[test]
fn test_parse_server_certificate_verify() {
    let cv = handshake_data(load_hex(server_certificate_verify));
    let res = parse_certificate_verify(&TLS_AES_128_GCM_SHA256_X25519_RSA, &cv);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(_) => {
            println!("Parsed CV!");
        }
    }
    assert!(b);
}

#[test]
fn test_parse_server_finished() {
    let sf = handshake_data(load_hex(server_finished));
    let res = parse_finished(&TLS_AES_128_GCM_SHA256_X25519_RSA, &sf);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(_) => {
            println!("Parsed SF!");
        }
    }
    assert!(b);
}

#[test]
fn test_parse_client_finished() {
    let cf = handshake_data(load_hex(client_finished));
    let res = parse_finished(&TLS_AES_128_GCM_SHA256_X25519_RSA, &cf);
    let b = res.is_ok();
    match res {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(_) => {
            println!("Parsed CF!");
        }
    }
    assert!(b);
}

#[test]
fn test_key_schedule() {
    let sha256_emp_str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
    let sha256_emp = load_hex(sha256_emp_str);
    match hash(&HashAlgorithm::SHA256, &Bytes::new(0)) {
        Ok(ha) => {
            println!(
                "computed hash(empty) {}\nexpected hash(empty) {}",
                ha.to_hex(),
                sha256_emp.to_hex()
            );
        }
        _ => {}
    }
    let ch: Bytes = load_hex(client_hello);
    let sh: Bytes = load_hex(server_hello);
    let ee: Bytes = load_hex(encrypted_extensions);
    let sc: Bytes = load_hex(server_certificate);
    let cv: Bytes = load_hex(server_certificate_verify);
    let sf: Bytes = load_hex(server_finished);
    let gxy: Key = Key::from_seq(&load_hex(shared_secret));
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = TLS_AES_128_GCM_SHA256_X25519_RSA;
    let tx = ch.concat(&sh);
    let tx_hash = hash(&ha, &tx);
    let mut b = true;
    match tx_hash {
        Err(x) => {
            println!("Error: {}", x);
        }
        Ok(tx_hash) => {
            let keys = derive_hk_ms(&ha, &ae, &gxy, &None, &tx_hash);
            b = keys.is_ok();
            match keys {
                Err(x) => {
                    println!("Error: {}", x);
                }
                Ok(((k1, iv1), (k2, iv2), cfk, sfk, ms)) => {
                    println!("Derive Succeeded!");
                    println!("chk: key {} \n iv {}", k1.to_hex(), iv1.to_hex());
                    println!("shk: key {} \n iv {}", k2.to_hex(), iv2.to_hex());
                    println!("cfk: {}", cfk.to_hex());
                    println!("sfk: {}", sfk.to_hex());
                    println!("ms: {}", ms.to_hex());
                    let tx = tx.concat(&ee).concat(&sc).concat(&cv).concat(&sf);
                    let tx_hash = hash(&ha, &tx);
                    match tx_hash {
                        Err(x) => {
                            println!("Error: {}", x);
                        }
                        Ok(tx_hash) => {
                            let keys = derive_app_keys(&ha, &ae, &ms, &tx_hash);
                            b = keys.is_ok();
                            match keys {
                                Err(x) => {
                                    println!("Error: {}", x);
                                }
                                Ok(((k1, iv1), (k2, iv2), ms)) => {
                                    println!("Derive Succeeded!");
                                    println!("cak: key {} \n iv {}", k1.to_hex(), iv1.to_hex());
                                    println!("sak: key {} \n iv {}", k2.to_hex(), iv2.to_hex());
                                    println!("exp: {}", ms.to_hex());
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(b);
}

#[test]
fn test_ecdh() {
    let x = load_hex(client_x25519_priv);
    let gx = load_hex(client_x25519_pub);
    let y = load_hex(server_x25519_priv);
    let gy = load_hex(server_x25519_pub);
    let gxy = load_hex(shared_secret);

    let my_gx = secret_to_public(&NamedGroup::X25519, &x);
    let my_gy = secret_to_public(&NamedGroup::X25519, &x);
    let my_ss1 = ecdh(&NamedGroup::X25519, &x, &gy);
    let my_ss2 = ecdh(&NamedGroup::X25519, &y, &gx);

    let mut b = true;
    match (my_gx, my_gy, my_ss1, my_ss2) {
        (Ok(gx_), Ok(gy_), Ok(ss1), Ok(ss2)) => {
            println!("expected gx {}", gx.to_hex());
            println!("computed gx {}", gx_.to_hex());
            println!("expected gy {}", gy.to_hex());
            println!("computed gy {}", gy_.to_hex());
            println!("expected ss {}", gxy.to_hex());
            println!("computed xy {}", ss1.to_hex());
            println!("computed yx {}", ss2.to_hex());
        }
        _ => {
            b = false;
        }
    }
    assert!(b);
}

const cfk_str: &str = "b80ad01015fb2f0bd65ff7d4da5d6bf83f84821d1f87fdc7d3c75b5a7b42d9c4";
const sfk_str: &str = "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8";

#[test]
fn test_finished() {
    let cfk = MacKey::from_seq(&load_hex(cfk_str));
    let sfk = MacKey::from_seq(&load_hex(sfk_str));

    let ch: Bytes = load_hex(client_hello);
    let sh: Bytes = load_hex(server_hello);
    let ee: Bytes = load_hex(encrypted_extensions);
    let sc: Bytes = load_hex(server_certificate);
    let cv: Bytes = load_hex(server_certificate_verify);
    let sf: Bytes = load_hex(server_finished);
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = TLS_AES_128_GCM_SHA256_X25519_RSA;
    let tx1 = ch.concat(&sh).concat(&ee).concat(&sc).concat(&cv);
    let tx_hash1 = hash(&ha, &tx1);
    let tx2 = tx1.concat(&sf);
    let tx_hash2 = hash(&ha, &tx2);
    let mut b = true;
    match (tx_hash1, tx_hash2) {
        (Ok(h1), Ok(h2)) => {
            let m1 = hmac_tag(&ha, &sfk, &h1);
            let m2 = hmac_tag(&ha, &cfk, &h2);
            match (m1, m2) {
                (Ok(m1), Ok(m2)) => {
                    println!("computed sfin vd {}", m1.to_hex());
                    println!("computed cfin vd {}", m2.to_hex());
                }
                _ => {
                    b = false;
                }
            }
        }
        _ => b = false,
    }
    assert!(b);
}

#[test]
fn test_full_round_trip() {
    let cr = Random::from_public_slice(&random_byte_vec(Random::length()));
    let x = load_hex(client_x25519_priv);
    let ent_c = Entropy::from_seq(&cr.concat(&x));
    let sn = load_hex("6c 6f 63 61 6c 68 6f 73 74");
    let sn_ = load_hex("6c 6f 63 61 6c 68 6f 73 74");
    let sr = Random::from_public_slice(&random_byte_vec(Random::length()));
    let y = load_hex(server_x25519_priv);
    let ent_s = Entropy::from_seq(&sr.concat(&y));

    let db = ServerDB(
        sn_,
        Bytes::from_public_slice(&ECDSA_P256_SHA256_CERT),
        SignatureKey::from_public_slice(&ECDSA_P256_SHA256_Key),
        None,
    );

    let mut b = true;
    match client_connect(TLS_AES_128_GCM_SHA256_X25519, &sn, None, None, ent_c) {
        Err(x) => {
            println!("Client0 Error {}", x);
            b = false;
        }
        Ok((ch, cstate)) => {
            println!("Client0 Complete");
            match server_accept(TLS_AES_128_GCM_SHA256_X25519, db, &ch, ent_s) {
                Err(x) => {
                    println!("ServerInit Error {}", x);
                    b = false;
                }
                Ok((sh, sf, sstate)) => {
                    println!("Server0 Complete");
                    match client_read_handshake(&sh, cstate) {
                        Err(x) => {
                            println!("ServerHello Error {}", x);
                            b = false;
                        },
                        Ok((Some(_),_)) =>{
                            println!("ServerHello State Error");
                            b = false;
                        },
                        Ok((None, cstate)) => match client_read_handshake(&sf, cstate) {
                            Err(x) => {
                                println!("ClientFinish Error {}", x);
                                b = false;
                            },
                            Ok((None,_)) =>{
                                println!("ClientFinish State Error");
                                b = false;
                            },
                            Ok((Some(cf), cstate)) => {
                                println!("Client Complete");
                                match server_read_handshake(&cf, sstate) {
                                    Err(x) => {
                                        println!("Server1 Error {}", x);
                                        b = false;
                                    }
                                    Ok(sstate) => {
                                        println!("Server Complete");

                                        // Send data from client to server.
                                        let data = Bytes::from_public_slice(
                                            b"Hello server, here is the client",
                                        );
                                        let (ap, cstate) =
                                            client_write(app_data(data.clone()), cstate)
                                                .unwrap();
                                        let (apo, sstate) =
                                            server_read(&ap, sstate).unwrap();
                                        assert_bytes_eq!(data, app_data_bytes(apo.unwrap()));

                                        // Send data from server to client.
                                        let data = Bytes::from_public_slice(
                                            b"Hello client, here is the server.",
                                        );
                                        let (ap, _sstate) =
                                            server_write(app_data(data.clone()), sstate)
                                                .unwrap();
                                        let (apo, _cstate) =
                                            client_read(&ap, cstate).unwrap();
                                        assert_bytes_eq!(data, app_data_bytes(apo.unwrap()));
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }
    }
    assert!(b);
}

use std::io;
use std::io::prelude::*;
use std::net::TcpStream;
use std::str;

//NOTES:
//OpenSSL divides up the server flight into multiple encrypted records, whereas most other servers send one big record
//We need to process the dummy CCS messages in the TCP layer
//Google divides messages into 1418-byte chunks and so sends 2 messages for the encrypted server flight

// use dhat::{Dhat, DhatAlloc};
// #[global_allocator]
// static ALLOCATOR: DhatAlloc = DhatAlloc;

#[test]
fn test_connect() {
    let mut b = true;
    match tls13client("www.google.com", "443") {
        Err(x) => {
            println!("Connection to www.google.com failed\n");
            b = false
        }
        Ok(x) => {
            println!("Connection to www.google.com succeeded\n");
        }
    }
    match tls13client("www.cloudflare.com", "443") {
        Err(x) => {
            println!("Connection to www.cloudflare.com failed\n");
            b = false
        }
        Ok(x) => {
            println!("Connection to www.cloudflare.com succeeded\n");
        }
    }
    assert!(b);
}
