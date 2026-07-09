import Benchmarks.Dss.Dog.Common

/-!
# MakerDAO/Sky DSS Dog trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

/-- `keccak("Dirt()")[0:4] = 0xeda6e121`. -/
axiom dirtSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr DirtTransition))).extract 0 4 =
      dogSelBytes 0

/-- `keccak("Hole()")[0:4] = 0xaf7cfeb1`. -/
axiom holeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr HoleTransition))).extract 0 4 =
      dogSelBytes 1

/-- `keccak("bark(bytes32,address,address)")[0:4] = 0xed998908`. -/
axiom barkSelectorBytes (v : DogImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (barkTransition v)))).extract 0 4 =
      dogSelBytes 2

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      dogSelBytes 3

/-- `keccak("chop(bytes32)")[0:4] = 0xd7926538`. -/
axiom chopSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr chopTransition))).extract 0 4 =
      dogSelBytes 4

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      dogSelBytes 5

/-- `keccak("digs(bytes32,uint256)")[0:4] = 0xc87193f4`. -/
axiom digsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr digsTransition))).extract 0 4 =
      dogSelBytes 6

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
axiom fileIlkUintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileIlkUintTransition))).extract 0 4 =
      dogSelBytes 7

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      dogSelBytes 8

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      dogSelBytes 9

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
axiom fileIlkClipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileIlkClipTransition))).extract 0 4 =
      dogSelBytes 10

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
axiom ilksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      dogSelBytes 11

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      dogSelBytes 12

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      dogSelBytes 13

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes (v : DogImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (vatTransition v)))).extract 0 4 =
      dogSelBytes 14

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      dogSelBytes 15

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      dogSelBytes 16

end Benchmarks.Dss.Dog
