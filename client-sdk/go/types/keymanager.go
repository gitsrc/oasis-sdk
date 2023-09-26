package types

import (
	"github.com/oasisprotocol/curve25519-voi/primitives/x25519"
	"github.com/oasisprotocol/oasis-core/go/common/crypto/signature"
)

// SignedPublicKey is the public key signed by the key manager.
type SignedPublicKey struct {
	// PublicKey is the requested public key.
	PublicKey x25519.PublicKey `json:"key"`
	// Checksum is the checksum of the key manager state.
	Checksum []byte `json:"checksum"`
	// Signature is the Sign(sk, (key || checksum)) from the key manager.
	Signature signature.RawSignature `json:"signature"`
}
