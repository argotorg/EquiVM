import Benchmarks.UniswapV3.Pool.FlashUpdateSource
import Benchmarks.UniswapV3.Pool.FlashRepaymentSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure FlashCoreValues (locals : Store) (recipient : AccountAddress)
    (amount0 amount1 liquidity : UInt256) : Prop where
  recipient : locals.get? "recipient" = some (.address recipient)
  amount0 : locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat))
  amount1 : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))
  liquidity : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat))
  slot0 : locals.get? "slot0" = none
  protocolFees : locals.get? "protocolFees" = none
  growth0 : locals.get? "feeGrowthGlobal0X128" = none
  growth1 : locals.get? "feeGrowthGlobal1X128" = none

def flashCoreNames : List Ident :=
  ["recipient", "amount0", "amount1", "_liquidity", "slot0", "protocolFees",
    "feeGrowthGlobal0X128", "feeGrowthGlobal1X128"]

theorem FlashCoreValues.of_get_eq {locals locals' : Store} {recipient : AccountAddress}
    {amount0 amount1 liquidity : UInt256}
    (hv : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (heq : ∀ name ∈ flashCoreNames, locals'.get? name = locals.get? name) :
    FlashCoreValues locals' recipient amount0 amount1 liquidity := by
  constructor
  · rw [heq "recipient" (by decide)]; exact hv.recipient
  · rw [heq "amount0" (by decide)]; exact hv.amount0
  · rw [heq "amount1" (by decide)]; exact hv.amount1
  · rw [heq "_liquidity" (by decide)]; exact hv.liquidity
  · rw [heq "slot0" (by decide)]; exact hv.slot0
  · rw [heq "protocolFees" (by decide)]; exact hv.protocolFees
  · rw [heq "feeGrowthGlobal0X128" (by decide)]; exact hv.growth0
  · rw [heq "feeGrowthGlobal1X128" (by decide)]; exact hv.growth1

theorem FlashCoreValues.insert {locals : Store} {recipient : AccountAddress}
    {amount0 amount1 liquidity : UInt256}
    (hv : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (name : Ident) (value : Value) (hn : name ∉ flashCoreNames) :
    FlashCoreValues (locals.insert name value) recipient amount0 amount1 liquidity := by
  apply hv.of_get_eq
  intro n hmem
  have hne : name ≠ n := fun h ↦ hn (h ▸ hmem)
  simp [Std.HashMap.getElem?_insert, hne]

theorem FlashCoreValues.update {locals locals' : Store} {recipient : AccountAddress}
    {amount0 amount1 liquidity : UInt256} {second : Bool}
    (hv : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (heq : FlashUpdatePreserves second locals locals') :
    FlashCoreValues locals' recipient amount0 amount1 liquidity := by
  apply hv.of_get_eq
  intro name hmem
  apply heq
  all_goals
    cases second <;>
      simp [flashCoreNames, flashProtocolName, flashProtocolFeesName, flashGrowthCallName] at hmem ⊢ <;>
      rcases hmem with h | h | h | h | h | h | h | h <;> subst name <;> decide

theorem FlashCoreValues.repaid {locals : Store} {recipient : AccountAddress}
    {amount0 amount1 liquidity : UInt256}
    (hv : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (v : UniswapV3PoolImmutables) (before0 before1 fee0 fee1 : UInt256) :
    FlashCoreValues (flashRepaidFrame v locals before0 before1 fee0 fee1).locals
      recipient amount0 amount1 liquidity :=
  (hv.insert "__c10" _ (by decide)).insert "__c11" _ (by decide)

theorem FlashCoreValues.paid {locals : Store} {recipient : AccountAddress}
    {amount0 amount1 liquidity : UInt256}
    (hv : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (v : UniswapV3PoolImmutables) (before0 before1 after0 after1 : UInt256) :
    FlashCoreValues (flashPaidFrame v locals before0 before1 after0 after1).locals
      recipient amount0 amount1 liquidity :=
  (hv.insert "paid0" _ (by decide)).insert "paid1" _ (by decide)

end Benchmarks.UniswapV3.Pool
