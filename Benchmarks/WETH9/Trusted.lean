import Benchmarks.WETH9.Common

/-!
# Trusted WETH9 selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`.  These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
They are the accepted selector/jump-dest trusted base for this benchmark.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.WETH9

/-- `keccak("name()")[0:4] = 0x06fdde03`. -/
axiom weth9NameSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr nameTransition))).extract 0 4
      = weth9SelBytes 0

/-- `keccak("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
axiom weth9ApproveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4
      = weth9SelBytes 1

/-- `keccak("totalSupply()")[0:4] = 0x18160ddd`. -/
axiom weth9TotalSupplySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4
      = weth9SelBytes 2

/-- `keccak("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
axiom weth9TransferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4
      = weth9SelBytes 3

/-- `keccak("withdraw(uint256)")[0:4] = 0x2e1a7d4d`. -/
axiom weth9WithdrawSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr withdrawTransition))).extract 0 4
      = weth9SelBytes 4

/-- `keccak("decimals()")[0:4] = 0x313ce567`. -/
axiom weth9DecimalsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr decimalsTransition))).extract 0 4
      = weth9SelBytes 5

/-- `keccak("balanceOf(address)")[0:4] = 0x70a08231`. -/
axiom weth9BalanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4
      = weth9SelBytes 6

/-- `keccak("symbol()")[0:4] = 0x95d89b41`. -/
axiom weth9SymbolSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr symbolTransition))).extract 0 4
      = weth9SelBytes 7

/-- `keccak("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
axiom weth9TransferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4
      = weth9SelBytes 8

/-- `keccak("deposit()")[0:4] = 0xd0e30db0`. -/
axiom weth9DepositSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr depositTransition))).extract 0 4
      = weth9SelBytes 9

/-- `keccak("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
axiom weth9AllowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4
      = weth9SelBytes 10

end Benchmarks.WETH9
