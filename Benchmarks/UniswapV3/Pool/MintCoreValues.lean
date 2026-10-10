import Benchmarks.UniswapV3.Pool.MintBeforeBalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure MintCoreValues (locals : Store) (a : MintArgs) (amount0 amount1 : UInt256) : Prop where
  recipient : locals.get? "recipient" = some (.address a.recipient)
  lower : locals.get? "tickLower" = some (.int a.lower)
  upper : locals.get? "tickUpper" = some (.int a.upper)
  amount : locals.get? "amount" = some (.int (Int.ofNat a.amount.toNat))
  amount0 : locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat))
  amount1 : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))
  data : locals.get? "data" = some (.bytes a.data)
  slot0 : locals.get? "slot0" = none

def mintCoreNames : List Ident :=
  ["recipient", "tickLower", "tickUpper", "amount", "amount0", "amount1", "data", "slot0"]

theorem MintCoreValues.insert {locals : Store} {a : MintArgs} {amount0 amount1 : UInt256}
    (hv : MintCoreValues locals a amount0 amount1) (name : Ident) (value : Value)
    (hn : name ∉ mintCoreNames) :
    MintCoreValues (locals.insert name value) a amount0 amount1 := by
  have hne (key : Ident) (hk : key ∈ mintCoreNames) : name ≠ key := fun h ↦ hn (h ▸ hk)
  constructor
  · simpa [Std.HashMap.getElem?_insert, hne "recipient" (by decide)] using hv.recipient
  · simpa [Std.HashMap.getElem?_insert, hne "tickLower" (by decide)] using hv.lower
  · simpa [Std.HashMap.getElem?_insert, hne "tickUpper" (by decide)] using hv.upper
  · simpa [Std.HashMap.getElem?_insert, hne "amount" (by decide)] using hv.amount
  · simpa [Std.HashMap.getElem?_insert, hne "amount0" (by decide)] using hv.amount0
  · simpa [Std.HashMap.getElem?_insert, hne "amount1" (by decide)] using hv.amount1
  · simpa [Std.HashMap.getElem?_insert, hne "data" (by decide)] using hv.data
  · simpa [Std.HashMap.getElem?_insert, hne "slot0" (by decide)] using hv.slot0

theorem mintCoreValues_initial (v : UniswapV3PoolImmutables) (a : MintArgs) (a0 a1 : Int) :
    MintCoreValues (mintBalancesInitFrame v a a0 a1).locals a
      (EVM.wordOfInt a0) (EVM.wordOfInt a1) := by
  constructor <;> simp only [mintBalancesInitFrame] <;> mint_amounts_get

end Benchmarks.UniswapV3.Pool
