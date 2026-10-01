import Benchmarks.Dss.Jug.Common

/-!
# MakerDAO/Sky DSS Jug selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("base()")[0:4] = 0x5001f3b5`. -/
theorem baseSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr baseTransition))).extract 0 4 =
      jugSelBytes 0 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      jugSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("drip(bytes32)")[0:4] = 0x44e2a5a8`. -/
theorem dripSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dripTransition))).extract 0 4 =
      jugSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, dripTransition, bytes32]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileBaseSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileBaseTransition))).extract 0 4 =
      jugSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileBaseTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
theorem fileDutySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileDutyTransition))).extract 0 4 =
      jugSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileDutyTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileVowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileVowTransition))).extract 0 4 =
      jugSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileVowTransition, bytes32, addr]; decide +kernel

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
theorem ilksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      jugSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ilksTransition, bytes32]; decide +kernel

/-- `keccak("init(bytes32)")[0:4] = 0x3b663195`. -/
theorem initSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr initTransition))).extract 0 4 =
      jugSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, initTransition, bytes32]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      jugSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      jugSelBytes 9 := by decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      jugSelBytes 10 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      jugSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Jug
