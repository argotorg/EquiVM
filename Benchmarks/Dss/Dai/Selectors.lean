import Benchmarks.Dss.Dai.Common

/-!
# Dai selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Dai

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
theorem daiAllowanceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4
      = daiSelBytes 0 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, allowanceTransition, addr]; decide +kernel

/-- `keccak("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
theorem daiApproveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4
      = daiSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, approveTransition, addr, uint256]; decide +kernel

/-- `keccak("balanceOf(address)")[0:4] = 0x70a08231`. -/
theorem daiBalanceOfSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4
      = daiSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, balanceOfTransition, addr]; decide +kernel

/-- `keccak("burn(address,uint256)")[0:4] = 0x9dc29fac`. -/
theorem daiBurnSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4
      = daiSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, burnTransition, addr, uint256]; decide +kernel

/-- `keccak("decimals()")[0:4] = 0x313ce567`. -/
theorem daiDecimalsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr decimalsTransition))).extract 0 4
      = daiSelBytes 4 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem daiDenySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4
      = daiSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("DOMAIN_SEPARATOR()")[0:4] = 0x3644e515`. -/
theorem daiDomainSeparatorSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr domainSeparatorTransition))).extract 0 4
      = daiSelBytes 6 := by decide +kernel

/-- `keccak("mint(address,uint256)")[0:4] = 0x40c10f19`. -/
theorem daiMintSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr mintTransition))).extract 0 4
      = daiSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, mintTransition, addr, uint256]; decide +kernel

/-- `keccak("move(address,address,uint256)")[0:4] = 0xbb35783b`. -/
theorem daiMoveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr moveTransition))).extract 0 4
      = daiSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, moveTransition, addr, uint256]; decide +kernel

/-- `keccak("name()")[0:4] = 0x06fdde03`. -/
theorem daiNameSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr nameTransition))).extract 0 4
      = daiSelBytes 9 := by decide +kernel

/-- `keccak("nonces(address)")[0:4] = 0x7ecebe00`. -/
theorem daiNoncesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr noncesTransition))).extract 0 4
      = daiSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, noncesTransition, addr]; decide +kernel

/-- `keccak("permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)")[0:4] =
    0x8fcbaf0c`. -/
theorem daiPermitSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr permitTransition))).extract 0 4
      = daiSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
    ABI.elemToSigStr, ABI.intTypeToSigStr, permitTransition, addr, uint256, uint256Int,
    boolTy, uint8, uint8Int, bytes32, bytes32Width]; decide +kernel

/-- `keccak("PERMIT_TYPEHASH()")[0:4] = 0x30adf81f`. -/
theorem daiPermitTypehashSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr permitTypehashTransition))).extract 0 4
      = daiSelBytes 12 := by decide +kernel

/-- `keccak("pull(address,uint256)")[0:4] = 0xf2d5d56b`. -/
theorem daiPullSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pullTransition))).extract 0 4
      = daiSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, pullTransition, addr, uint256]; decide +kernel

/-- `keccak("push(address,uint256)")[0:4] = 0xb753a98c`. -/
theorem daiPushSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pushTransition))).extract 0 4
      = daiSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, pushTransition, addr, uint256]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem daiRelySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4
      = daiSelBytes 15 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("symbol()")[0:4] = 0x95d89b41`. -/
theorem daiSymbolSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr symbolTransition))).extract 0 4
      = daiSelBytes 16 := by decide +kernel

/-- `keccak("totalSupply()")[0:4] = 0x18160ddd`. -/
theorem daiTotalSupplySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4
      = daiSelBytes 17 := by decide +kernel

/-- `keccak("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
theorem daiTransferSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4
      = daiSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, transferTransition, addr, uint256]; decide +kernel

/-- `keccak("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
theorem daiTransferFromSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4
      = daiSelBytes 19 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, transferFromTransition, addr, uint256]; decide +kernel

/-- `keccak("version()")[0:4] = 0x54fd4d50`. -/
theorem daiVersionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr versionTransition))).extract 0 4
      = daiSelBytes 20 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem daiWardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4
      = daiSelBytes 21 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Dai
