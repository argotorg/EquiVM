import Benchmarks.Dss.DaiJoin.Common

/-!
# MakerDAO/Sky DSS DaiJoin selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.DaiJoin

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      daiJoinSelBytes 0 := by decide +kernel

/-- `keccak("dai()")[0:4] = 0xf4b9fa75`. -/
theorem daiSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr daiTransition))).extract 0 4 =
      daiJoinSelBytes 1 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      daiJoinSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("exit(address,uint256)")[0:4] = 0xef693bed`. -/
theorem exitSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      daiJoinSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, exitTransition, addr, uint256]; decide +kernel

/-- `keccak("join(address,uint256)")[0:4] = 0x3b4da69f`. -/
theorem joinSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      daiJoinSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, joinTransition, addr, uint256]; decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      daiJoinSelBytes 5 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      daiJoinSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      daiJoinSelBytes 7 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      daiJoinSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.DaiJoin
