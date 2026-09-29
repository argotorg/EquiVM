import Benchmarks.Dss.GemJoin.Common

/-!
# Trusted selector facts for MakerDAO/Sky DSS GemJoin

These are the ABI selector facts accepted by the benchmark prompt.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.GemJoin

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem gemJoinCageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      gemJoinSelBytes 0 := by decide +kernel

/-- `keccak("dec()")[0:4] = 0xb3bcfa82`. -/
theorem gemJoinDecSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr decTransition))).extract 0 4 =
      gemJoinSelBytes 1 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem gemJoinDenySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      gemJoinSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("exit(address,uint256)")[0:4] = 0xef693bed`. -/
theorem gemJoinExitSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      gemJoinSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, exitTransition, addr, uint256]; decide +kernel

/-- `keccak("gem()")[0:4] = 0x7bd2bea7`. -/
theorem gemJoinGemSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      gemJoinSelBytes 4 := by decide +kernel

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
theorem gemJoinIlkSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilkTransition))).extract 0 4 =
      gemJoinSelBytes 5 := by decide +kernel

/-- `keccak("join(address,uint256)")[0:4] = 0x3b4da69f`. -/
theorem gemJoinJoinSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      gemJoinSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, joinTransition, addr, uint256]; decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem gemJoinLiveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      gemJoinSelBytes 7 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem gemJoinRelySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      gemJoinSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem gemJoinVatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      gemJoinSelBytes 9 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem gemJoinWardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      gemJoinSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.GemJoin
