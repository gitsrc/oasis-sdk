package helpers

import (
	"encoding/hex"
	"fmt"
	"strings"

	"golang.org/x/crypto/sha3"

	staking "github.com/oasisprotocol/oasis-core/go/staking/api"

	"github.com/oasisprotocol/oasis-sdk/client-sdk/go/config"
	"github.com/oasisprotocol/oasis-sdk/client-sdk/go/crypto/signature/secp256k1"
	"github.com/oasisprotocol/oasis-sdk/client-sdk/go/modules/rewards"
	"github.com/oasisprotocol/oasis-sdk/client-sdk/go/testing"
	"github.com/oasisprotocol/oasis-sdk/client-sdk/go/types"
)

const (
	addressPrefixOasis = "oasis1"
	addressPrefixEth   = "0x"

	addressExplicitSeparator = ":"
	addressExplicitParaTime  = "paratime"
	addressExplicitPool      = "pool"
	addressExplicitTest      = "test"

	poolRewards = "rewards"
)

// ResolveAddress resolves a string address into the corresponding account address.
func ResolveAddress(net *config.Network, address string) (*types.Address, error) {
	switch {
	case strings.HasPrefix(address, addressPrefixOasis):
		// Oasis Bech32 address.
		var a types.Address
		if err := a.UnmarshalText([]byte(address)); err != nil {
			return nil, err
		}
		return &a, nil
	case strings.HasPrefix(address, addressPrefixEth):
		// Ethereum address, derive Oasis Bech32 address.
		ethAddr, err := hex.DecodeString(address[2:])
		if err != nil {
			return nil, fmt.Errorf("malformed Ethereum address: %w", err)
		}
		if len(ethAddr) != 20 {
			return nil, fmt.Errorf("malformed Ethereum address: expected 20 bytes")
		}
		addr := types.NewAddressRaw(types.AddressV0Secp256k1EthContext, ethAddr)
		return &addr, nil
	case strings.Contains(address, addressExplicitSeparator):
		subs := strings.SplitN(address, addressExplicitSeparator, 2)
		switch kind, data := subs[0], subs[1]; kind {
		case addressExplicitParaTime:
			// ParaTime.
			pt := net.ParaTimes.All[data]
			if pt == nil {
				return nil, fmt.Errorf("paratime '%s' does not exist", data)
			}

			addr := types.NewAddressFromConsensus(staking.NewRuntimeAddress(pt.Namespace()))
			return &addr, nil
		case addressExplicitPool:
			// Pool.
			switch data {
			case poolRewards:
				// Reward pool address.
				return &rewards.RewardPoolAddress, nil
			default:
				return nil, fmt.Errorf("unsupported pool kind: %s", data)
			}
		case addressExplicitTest:
			// Test key.
			if testKey, ok := testing.TestAccounts[data]; ok {
				return &testKey.Address, nil
			}
			return nil, fmt.Errorf("unsupported test account: %s", data)
		default:
			// Unsupported kind.
			return nil, fmt.Errorf("unsupported explicit address kind: %s", kind)
		}
	default:
		return nil, fmt.Errorf("unsupported address format")
	}
}

// ParseTestAccountAddress extracts test account name from "test:some_test_account" format or
// returns an empty string, if the format doesn't match.
func ParseTestAccountAddress(name string) string {
	if strings.Contains(name, addressExplicitSeparator) {
		subs := strings.SplitN(name, addressExplicitSeparator, 2)
		if subs[0] == addressExplicitTest {
			return subs[1]
		}
	}

	return ""
}

// EthAddressFromPubKey takes public key, extracts the ethereum address and returns its checksummed
// case-sensitive variant.
func EthAddressFromPubKey(pk secp256k1.PublicKey) string {
	h := sha3.NewLegacyKeccak256()
	untaggedPk, _ := pk.MarshalBinaryUncompressedUntagged()
	h.Write(untaggedPk)
	hash := h.Sum(nil)
	unchecksummed := hex.EncodeToString(hash[32-20:])

	sha := sha3.NewLegacyKeccak256()
	sha.Write([]byte(unchecksummed))
	hash = sha.Sum(nil)

	result := []byte(unchecksummed)
	for i := 0; i < len(result); i++ {
		hashByte := hash[i/2]
		if i%2 == 0 {
			hashByte >>= 4
		} else {
			hashByte &= 0xf
		}
		if result[i] > '9' && hashByte > 7 {
			result[i] -= 32
		}
	}
	return fmt.Sprintf("0x%s", string(result))
}
