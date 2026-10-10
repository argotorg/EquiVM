import Benchmarks.UniswapV3.Pool.MintCoreValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure MintCallValues (locals : Store) (a : MintArgs)
    (amount0 amount1 before0 before1 : UInt256) : Prop where
  core : MintCoreValues locals a amount0 amount1
  before0 : locals.get? "balance0Before" = some (.int (Int.ofNat before0.toNat))
  before1 : locals.get? "balance1Before" = some (.int (Int.ofNat before1.toNat))

def mintCallNames : List Ident := mintCoreNames ++ ["balance0Before", "balance1Before"]

theorem MintCallValues.insert {locals : Store} {a : MintArgs}
    {amount0 amount1 before0 before1 : UInt256}
    (hv : MintCallValues locals a amount0 amount1 before0 before1) (name : Ident) (value : Value)
    (hn : name ∉ mintCallNames) :
    MintCallValues (locals.insert name value) a amount0 amount1 before0 before1 := by
  have hne (key : Ident) (hk : key ∈ mintCallNames) : name ≠ key := fun h ↦ hn (h ▸ hk)
  refine ⟨hv.core.insert name value (fun h ↦ hn (List.mem_append_left _ h)), ?_, ?_⟩
  · simpa [Std.HashMap.getElem?_insert, hne "balance0Before" (by decide)] using hv.before0
  · simpa [Std.HashMap.getElem?_insert, hne "balance1Before" (by decide)] using hv.before1

theorem MintCallValues.beforeBalance {locals : Store} {a : MintArgs}
    {amount0 amount1 before0 before1 : UInt256}
    (hv : MintCallValues locals a amount0 amount1 before0 before1)
    (v : UniswapV3PoolImmutables) (second : Bool) (balance : UInt256)
    (hz : (if second then amount1 else amount0) = ⟨0⟩ →
      balance = (if second then before1 else before0)) :
    MintCallValues (mintBeforeBalanceFrame v locals second
      (if second then amount1 else amount0) balance).locals a amount0 amount1
      (if second then before0 else balance) (if second then balance else before1) := by
  cases second with
  | false =>
    by_cases h0 : amount0 = ⟨0⟩
    · simpa only [mintBeforeBalanceFrame, mintBeforeBalanceLocals, Bool.false_eq_true,
        ↓reduceIte, if_pos h0, hz h0] using hv
    · simp only [mintBeforeBalanceFrame, mintBeforeBalanceLocals, Bool.false_eq_true,
        ↓reduceIte, if_neg h0, mintBeforeBalanceName, mintBeforeBalanceTemp]
      refine ⟨(hv.core.insert "__c2" _ (by decide)).insert "balance0Before" _ (by decide), ?_, ?_⟩
      · simp
      · simpa [Std.HashMap.getElem?_insert] using hv.before1
  | true =>
    by_cases h1 : amount1 = ⟨0⟩
    · simpa only [mintBeforeBalanceFrame, mintBeforeBalanceLocals,
        ↓reduceIte, if_pos h1, hz h1] using hv
    · simp only [mintBeforeBalanceFrame, mintBeforeBalanceLocals,
        ↓reduceIte, if_neg h1, mintBeforeBalanceName, mintBeforeBalanceTemp]
      refine ⟨(hv.core.insert "__c3" _ (by decide)).insert "balance1Before" _ (by decide), ?_, ?_⟩
      · simpa [Std.HashMap.getElem?_insert] using hv.before0
      · simp

theorem mintCallValues_initial (v : UniswapV3PoolImmutables) (a : MintArgs) (a0 a1 : Int) :
    MintCallValues (mintBalancesInitFrame v a a0 a1).locals a
      (EVM.wordOfInt a0) (EVM.wordOfInt a1) ⟨0⟩ ⟨0⟩ := by
  refine ⟨mintCoreValues_initial v a a0 a1, ?_, ?_⟩ <;>
    simp only [mintBalancesInitFrame] <;> mint_amounts_get

end Benchmarks.UniswapV3.Pool
