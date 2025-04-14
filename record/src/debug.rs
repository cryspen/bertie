use std::fmt::{Display, Formatter};

use t13::{get_hs_type, AlertDescription, AlertLevel, ContentType};
use tracing::{error, info};

/// For debugging only.
pub fn info_record(record: &[u8]) {
    if !record.is_empty() {
        let content_type = ContentType::try_from_u8(record[0]);

        match content_type {
            Ok(ContentType::Handshake) => {
                if record.len() >= 6 {
                    let handshake_type = get_hs_type(record[5]);
                    info!(?content_type, ?handshake_type, "TLS record.");
                } else {
                    error!("Record incomplete.");
                }
            }
            Ok(ContentType::Alert) => {
                if record.len() >= 7 {
                    let alert_type = AlertLevel::try_from(record[5]);
                    let alert_description = AlertDescription::try_from(record[6]);
                    info!(
                        ?content_type,
                        ?alert_type,
                        ?alert_description,
                        "TLS record."
                    );
                } else {
                    error!("Record incomplete.");
                }
            }
            _ => {
                info!(?content_type, "TLS record.");
            }
        }
    } else {
        error!("Record incomplete.");
    }
}

pub struct Hex<'a>(pub &'a [u8]);

impl Display for Hex<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}
