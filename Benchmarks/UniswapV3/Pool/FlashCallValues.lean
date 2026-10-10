import Benchmarks.UniswapV3.Pool.FlashValues
import Benchmarks.UniswapV3.Pool.FlashTransfer
import Benchmarks.UniswapV3.Pool.FlashCallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure FlashCallValues (locals : Store) (a : FlashArgs)
    (liquidity fee0 fee1 before0 before1 : UInt256) : Prop where
  core : FlashCoreValues locals a.recipient a.amount0 a.amount1 liquidity
  fee0 : locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat))
  fee1 : locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat))
  before0 : locals.get? "balance0Before" = some (.int (Int.ofNat before0.toNat))
  before1 : locals.get? "balance1Before" = some (.int (Int.ofNat before1.toNat))
  data : locals.get? "data" = some (.bytes a.data)

def flashCallNames : List Ident :=
  flashCoreNames ++ ["fee0", "fee1", "balance0Before", "balance1Before", "data"]

theorem FlashCallValues.insert {locals : Store} {a : FlashArgs}
    {liquidity fee0 fee1 before0 before1 : UInt256}
    (hv : FlashCallValues locals a liquidity fee0 fee1 before0 before1)
    (name : Ident) (value : Value) (hn : name ∉ flashCallNames) :
    FlashCallValues (locals.insert name value) a liquidity fee0 fee1 before0 before1 := by
  have hne (key : Ident) (hk : key ∈ flashCallNames) : name ≠ key := fun h ↦ hn (h ▸ hk)
  refine ⟨hv.core.insert name value (fun h ↦ hn (List.mem_append_left _ h)), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Std.HashMap.getElem?_insert, hne "fee0" (by decide)] using hv.fee0
  · simpa [Std.HashMap.getElem?_insert, hne "fee1" (by decide)] using hv.fee1
  · simpa [Std.HashMap.getElem?_insert, hne "balance0Before" (by decide)] using hv.before0
  · simpa [Std.HashMap.getElem?_insert, hne "balance1Before" (by decide)] using hv.before1
  · simpa [Std.HashMap.getElem?_insert, hne "data" (by decide)] using hv.data

theorem FlashCallValues.transfer {locals : Store} {a : FlashArgs}
    {liquidity fee0 fee1 before0 before1 : UInt256}
    (hv : FlashCallValues locals a liquidity fee0 fee1 before0 before1)
    (second : Bool) (amount : UInt256) :
    FlashCallValues (flashTransferLocals locals second amount) a liquidity fee0 fee1 before0 before1 := by
  by_cases hz : amount = ⟨0⟩
  · simpa only [flashTransferLocals, if_pos hz] using hv
  · exact (by simpa only [flashTransferLocals, if_neg hz] using
      hv.insert (flashTransferName second) .unit (by cases second <;> decide))

theorem FlashCallValues.callback {frame : Frame} {a : FlashArgs}
    {liquidity fee0 fee1 before0 before1 : UInt256}
    (hv : FlashCallValues frame.locals a liquidity fee0 fee1 before0 before1)
    (target : AccountAddress) :
    FlashCallValues (flashCallbackDoneFrame frame target).locals a liquidity fee0 fee1 before0 before1 :=
  (hv.insert "callback" (.address target) (by decide)).insert "__c7" .unit (by decide)

theorem FlashCallValues.balances {locals : Store} {a : FlashArgs}
    {liquidity fee0 fee1 before0 before1 : UInt256}
    (hv : FlashCallValues locals a liquidity fee0 fee1 before0 before1)
    (v : UniswapV3PoolImmutables) (after0 after1 : UInt256) :
    FlashCoreValues (flashBalancesFrame v locals true after0 after1).locals
        a.recipient a.amount0 a.amount1 liquidity ∧
      FlashRepayValues (flashBalancesFrame v locals true after0 after1).locals
        before0 before1 fee0 fee1 after0 after1 := by
  refine ⟨(hv.core.insert "balance0After" _ (by decide)).insert "balance1After" _ (by decide), ?_⟩
  constructor
  · simpa [flashBalancesFrame, flashBalanceName, Std.HashMap.getElem?_insert] using hv.before0
  · simpa [flashBalancesFrame, flashBalanceName, Std.HashMap.getElem?_insert] using hv.before1
  · simpa [flashBalancesFrame, flashBalanceName, Std.HashMap.getElem?_insert] using hv.fee0
  · simpa [flashBalancesFrame, flashBalanceName, Std.HashMap.getElem?_insert] using hv.fee1
  · simp [flashBalancesFrame, flashBalanceName, Std.HashMap.getElem_insert]
  · simp [flashBalancesFrame, flashBalanceName]

theorem flashCallValues_initial (v : UniswapV3PoolImmutables) (a : FlashArgs)
    (liquidity fee0 fee1 before0 before1 : UInt256) :
    FlashCallValues (flashBalancesFrame v (flashFeesFrame v a liquidity fee0 fee1).locals
      false before0 before1).locals a liquidity fee0 fee1 before0 before1 := by
  constructor
  · constructor <;>
      simp [flashBalancesFrame, flashBalanceName, flashFeesFrame, flashFee0Frame, flashReadyFrame,
        flashCheckedFrame, flashFrame, flashLocals, Std.HashMap.getElem_insert]
  all_goals simp [flashBalancesFrame, flashBalanceName, flashFeesFrame, flashFee0Frame, flashReadyFrame,
    flashCheckedFrame, flashFrame, flashLocals, Std.HashMap.getElem_insert]

end Benchmarks.UniswapV3.Pool
