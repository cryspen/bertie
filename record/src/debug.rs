use std::fmt::{Display, Formatter};

use bertie::{get_alert_description, get_alert_level, get_content_type, get_hs_type, ContentType};
use tracing::{error, info};

/// For debugging only.
pub fn info_record(record: &[u8]) {
    if !record.is_empty() {
        let content_type = get_content_type(record[0]);

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
                    let alert_type = get_alert_level(record[5]);
                    let alert_description = get_alert_description(record[6]);
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

impl<'a> Display for Hex<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}
