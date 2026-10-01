import Benchmarks.Dss.Dog.Common

/-!
# MakerDAO/Sky DSS Dog selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("Dirt()")[0:4] = 0xeda6e121`. -/
theorem dirtSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr DirtTransition))).extract 0 4 =
      dogSelBytes 0 := by decide +kernel

/-- `keccak("Hole()")[0:4] = 0xaf7cfeb1`. -/
theorem holeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr HoleTransition))).extract 0 4 =
      dogSelBytes 1 := by decide +kernel

/-- `keccak("bark(bytes32,address,address)")[0:4] = 0xed998908`. -/
theorem barkSelectorBytes (v : DogImmutables) :
    (KEC (String.toByteArray (transitionSigStr (barkTransition v)))).extract 0 4 =
      dogSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, barkTransition, bytes32, addr]; decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      dogSelBytes 3 := by decide +kernel

/-- `keccak("chop(bytes32)")[0:4] = 0xd7926538`. -/
theorem chopSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr chopTransition))).extract 0 4 =
      dogSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, chopTransition, bytes32]; decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      dogSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("digs(bytes32,uint256)")[0:4] = 0xc87193f4`. -/
theorem digsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr digsTransition))).extract 0 4 =
      dogSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, digsTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
theorem fileIlkUintSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileIlkUintTransition))).extract 0 4 =
      dogSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileIlkUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileUintSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      dogSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileAddressSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      dogSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
theorem fileIlkClipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileIlkClipTransition))).extract 0 4 =
      dogSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileIlkClipTransition, bytes32, addr]; decide +kernel

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
theorem ilksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      dogSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ilksTransition, bytes32]; decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      dogSelBytes 12 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      dogSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes (v : DogImmutables) :
    (KEC (String.toByteArray (transitionSigStr (vatTransition v)))).extract 0 4 =
      dogSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, vatTransition]; decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      dogSelBytes 15 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      dogSelBytes 16 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Dog
