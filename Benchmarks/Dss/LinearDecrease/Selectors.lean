import Benchmarks.Dss.LinearDecrease.Common

/-!
# MakerDAO/Sky DSS LinearDecrease selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.LinearDecrease

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      stairstepSelBytes 0 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileTransition))).extract 0 4 =
      stairstepSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileTransition, bytes32, uint256]; decide +kernel

/-- `keccak("price(uint256,uint256)")[0:4] = 0x487a2395`. -/
theorem priceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr priceTransition))).extract 0 4 =
      stairstepSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, priceTransition, uint256]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      stairstepSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
theorem tauSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      stairstepSelBytes 4 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      stairstepSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.LinearDecrease
