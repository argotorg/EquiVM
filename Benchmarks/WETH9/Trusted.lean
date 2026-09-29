import Benchmarks.WETH9.Common

/-!
# Trusted WETH9 selector facts

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.WETH9

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("name()")[0:4] = 0x06fdde03`. -/
theorem weth9NameSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr nameTransition))).extract 0 4
      = weth9SelBytes 0 := by decide +kernel

/-- `keccak("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
theorem weth9ApproveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4
      = weth9SelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, approveTransition, addr, uint256]; decide +kernel

/-- `keccak("totalSupply()")[0:4] = 0x18160ddd`. -/
theorem weth9TotalSupplySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4
      = weth9SelBytes 2 := by decide +kernel

/-- `keccak("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
theorem weth9TransferFromSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4
      = weth9SelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, transferFromTransition, addr, uint256]; decide +kernel

/-- `keccak("withdraw(uint256)")[0:4] = 0x2e1a7d4d`. -/
theorem weth9WithdrawSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr withdrawTransition))).extract 0 4
      = weth9SelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, withdrawTransition, uint256]; decide +kernel

/-- `keccak("decimals()")[0:4] = 0x313ce567`. -/
theorem weth9DecimalsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr decimalsTransition))).extract 0 4
      = weth9SelBytes 5 := by decide +kernel

/-- `keccak("balanceOf(address)")[0:4] = 0x70a08231`. -/
theorem weth9BalanceOfSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4
      = weth9SelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, balanceOfTransition, addr]; decide +kernel

/-- `keccak("symbol()")[0:4] = 0x95d89b41`. -/
theorem weth9SymbolSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr symbolTransition))).extract 0 4
      = weth9SelBytes 7 := by decide +kernel

/-- `keccak("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
theorem weth9TransferSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4
      = weth9SelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, transferTransition, addr, uint256]; decide +kernel

/-- `keccak("deposit()")[0:4] = 0xd0e30db0`. -/
theorem weth9DepositSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr depositTransition))).extract 0 4
      = weth9SelBytes 9 := by decide +kernel

/-- `keccak("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
theorem weth9AllowanceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4
      = weth9SelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, allowanceTransition, addr]; decide +kernel

end Benchmarks.WETH9
