import Benchmarks.UniswapV3.Pool.BalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem poolBalanceReturns (v : UniswapV3PoolImmutables) (locals : Store) (name : Ident)
    (evm evm' : EVM.State) (second : Bool) (value : UInt256) (calleeFrame : Frame)
    (hcall : ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v}
      evm (balanceFunction second).body
      (.returned calleeFrame evm' (some [.int (Int.ofNat value.toNat)]))) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (.internalCall (if second then "balance1" else "balance0") [] name)
      (.ok { contract := contract
             locals := locals.insert name (.int (Int.ofNat value.toNat))
             immutables := immStore v } evm') :=
  internalCallFunctionReturn (callee := balanceFunction second) (locals := ∅)
    (calleeSolm := calleeFrame) (value := some [.int (Int.ofNat value.toNat)])
    (by simp only [evalExprs?, pure]) (balanceLookup second) (balanceBind second) hcall

theorem poolBalanceReverts (v : UniswapV3PoolImmutables) (locals : Store) (name : Ident)
    (evm : EVM.State) (second : Bool)
    (hcall : ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v}
      evm (balanceFunction second).body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (.internalCall (if second then "balance1" else "balance0") [] name) .reverted :=
  internalCallFunctionRevert (callee := balanceFunction second) (locals := ∅)
    (by simp only [evalExprs?, pure]) (balanceLookup second) (balanceBind second) hcall

end Benchmarks.UniswapV3.Pool
