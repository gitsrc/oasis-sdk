//! Types related to call formats.
use crate::core::common::crypto::{mrae::deoxysii, x25519};

/// Call data key pair ID domain separation context base.
pub const CALL_DATA_KEY_PAIR_ID_CONTEXT_BASE: &[u8] = b"oasis-runtime-sdk/private: tx";

/// A call envelope when using the EncryptedX25519DeoxysII format.
#[derive(Clone, Debug, Default, cbor::Encode, cbor::Decode)]
pub struct CallEnvelopeX25519DeoxysII {
    /// Caller's ephemeral public key used for X25519.
    pub pk: x25519::PublicKey,
    /// Nonce.
    pub nonce: [u8; deoxysii::NONCE_SIZE],
    /// Epoch of the ephemeral runtime key.
    #[cbor(optional)]
    pub epoch: u64,
    /// Encrypted call data.
    pub data: Vec<u8>,
}

/// A result envelope when using the EncryptedX25519DeoxysII format.
#[derive(Clone, Debug, Default, cbor::Encode, cbor::Decode)]
pub struct ResultEnvelopeX25519DeoxysII {
    /// Nonce.
    pub nonce: [u8; deoxysii::NONCE_SIZE],
    /// Encrypted call data.
    pub data: Vec<u8>,
}
