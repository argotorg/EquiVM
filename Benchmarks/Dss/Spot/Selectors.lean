import Benchmarks.Dss.Spot.Common

/-!
# MakerDAO/Sky DSS Spotter selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Spot

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      spotSelBytes 0 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      spotSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
theorem fileMatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileMatTransition))).extract 0 4 =
      spotSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileMatTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileParSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileParTransition))).extract 0 4 =
      spotSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileParTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
theorem filePipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr filePipTransition))).extract 0 4 =
      spotSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, filePipTransition, bytes32, addr]; decide +kernel

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
theorem ilksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      spotSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ilksTransition, bytes32]; decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      spotSelBytes 6 := by decide +kernel

/-- `keccak("par()")[0:4] = 0x495d32cb`. -/
theorem parSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr parTransition))).extract 0 4 =
      spotSelBytes 7 := by decide +kernel

/-- `keccak("poke(bytes32)")[0:4] = 0x1504460f`. -/
theorem pokeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pokeTransition))).extract 0 4 =
      spotSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, pokeTransition, bytes32]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      spotSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      spotSelBytes 10 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      spotSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Spot
