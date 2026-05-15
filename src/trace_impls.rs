//! `TraceArg` / `TraceOutput` impls for Bertie's wire-message types.
//!
//! Lives behind the `trace` feature. When this feature is enabled, the
//! `#[traced(serializer)]` annotations on Bertie's `tls13formats` serializer
//! functions register a `Term::Struct { type_name: <fn>, fields: <args> }`
//! against the output bytes' fingerprint in the active
//! `symbolic_trace::session::TracerSession`. Downstream `network_sink`
//! events (and any AEAD encrypt that wraps the bytes) then resolve to that
//! rich call term instead of an opaque `Literal`.

use std::format;
use std::vec::Vec;

use symbolic_trace::term::Term;
use symbolic_trace::trace_arg::{TraceArg, TraceOutput};

use crate::tls13crypto::{
    AeadAlgorithm, AeadKey, Algorithms, HashAlgorithm, KemScheme, PublicVerificationKey,
    SignatureScheme,
};
use crate::tls13formats::handshake_data::HandshakeData;
use crate::tls13formats::ContentType;
use crate::tls13utils::Bytes;

fn bytes_to_term(raw: &[u8]) -> Term {
    symbolic_trace::session::with_session(|s| s.shadow.lookup_or_literal(raw))
        .unwrap_or_else(|| Term::literal_from_bytes(raw))
}

// ---------- TraceArg impls (byte-shaped values) ----------

impl TraceArg for Bytes {
    fn trace_term(&self) -> Term {
        bytes_to_term(&self.declassify())
    }
}

impl TraceArg for HandshakeData {
    fn trace_term(&self) -> Term {
        bytes_to_term(&self.to_bytes().declassify())
    }
}

// ---------- TraceArg impls (value-shaped — emit Term::Scalar) ----------

impl TraceArg for Algorithms {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::json!({
                "hash": format!("{:?}", self.hash()),
                "aead": format!("{:?}", self.aead()),
                "signature": format!("{:?}", self.signature()),
                "kem": format!("{:?}", self.kem()),
                "psk_mode": self.psk_mode(),
                "zero_rtt": self.zero_rtt(),
            }),
        }
    }
}

impl TraceArg for HashAlgorithm {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::Value::String(format!("{:?}", self)),
        }
    }
}

impl TraceArg for AeadAlgorithm {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::Value::String(format!("{:?}", self)),
        }
    }
}

impl TraceArg for SignatureScheme {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::Value::String(format!("{:?}", self)),
        }
    }
}

impl TraceArg for KemScheme {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::Value::String(format!("{:?}", self)),
        }
    }
}

impl TraceArg for PublicVerificationKey {
    fn trace_term(&self) -> Term {
        match self {
            PublicVerificationKey::EcDsa(b) => bytes_to_term(&b.declassify()),
            PublicVerificationKey::Rsa(rsa) => {
                let mut v = rsa.modulus.declassify();
                v.extend_from_slice(&rsa.exponent.declassify());
                bytes_to_term(&v)
            }
        }
    }
}

impl TraceArg for AeadKey {
    fn trace_term(&self) -> Term {
        bytes_to_term(&self.bytes().declassify())
    }
}

impl TraceArg for crate::tls13crypto::AeadKeyIV {
    fn trace_term(&self) -> Term {
        let mut fields = Vec::with_capacity(2);
        fields.push((format!("key"), bytes_to_term(&self.key.bytes().declassify())));
        fields.push((format!("iv"), bytes_to_term(&self.iv.declassify())));
        Term::Struct {
            type_name: format!("AeadKeyIV"),
            fields,
        }
    }
}

impl TraceArg for ContentType {
    fn trace_term(&self) -> Term {
        Term::Scalar {
            value: serde_json::Value::String(format!("{:?}", self)),
        }
    }
}

// ---------- TraceOutput impls ----------

impl TraceOutput for Bytes {
    fn trace_output_bytes(&self) -> Option<Vec<u8>> {
        Some(self.declassify())
    }
}

impl TraceOutput for HandshakeData {
    fn trace_output_bytes(&self) -> Option<Vec<u8>> {
        Some(self.to_bytes().declassify())
    }
}
