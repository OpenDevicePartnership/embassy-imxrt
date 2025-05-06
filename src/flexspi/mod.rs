pub mod nor;

#[cfg(feature = "time")]
use embassy_time::Instant;

#[cfg(feature = "time")]
pub(crate) fn is_expired(start: Instant, timeout: u64) -> bool {
    Instant::now().duration_since(start).as_millis() > timeout
}
