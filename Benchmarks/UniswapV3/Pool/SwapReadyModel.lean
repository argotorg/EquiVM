import Benchmarks.UniswapV3.Pool.SwapReadyTrace
import Benchmarks.UniswapV3.Pool.SwapMemoryModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCacheInitial_words {s0 evm : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    (a : SwapArgs) (hs : SourceState s0 ee σ evm) :
    (swapCacheInitial a evm).words =
      swapCacheInitWords (poolProtocolDivisor (!a.zeroForOne) σ ee)
        (storeSlot0Unlocked evm false).accountMap ee := by
  simp only [swapCacheInitial, SwapCacheData.words, swapCacheInitWords,
    ← hs.accounts, hs.env]
  rfl

theorem swapStateInitial_words {s0 evm : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    (a : SwapArgs) (hs : SourceState s0 ee σ evm) :
    (swapStateInitial a evm).words =
      swapStateInitWords (EVM.wordOfInt a.amountSpecified) (slot0FieldWord 0 20 σ ee)
        (EVM.wordOfInt (slot0TickValue σ ee))
        (feeGrowthWord (!a.zeroForOne) (storeSlot0Unlocked evm false).accountMap ee)
        (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap ee) := by
  simp only [swapStateInitial, SwapStateData.words, swapStateInitWords, swapCacheInitial,
    ← hs.accounts, hs.env]
  rfl

theorem swapInitializedMem_state {s0 evm : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {mem : ByteArray} {p : UInt256} (a : SwapArgs) (hs : SourceState s0 ee σ evm)
    (hp : 128 ≤ p.toNat) (hb : p.toNat + 416 ≤ 2 ^ 200) :
    SwapStateMemory
      (swapInitializedMem mem p (poolProtocolDivisor (!a.zeroForOne) σ ee) a
        (storeSlot0Unlocked evm false).accountMap σ ee)
      (p + UInt256.ofNat 192) (swapStateInitial a evm) := by
  unfold SwapStateMemory
  rw [swapStateInitial_words a hs]
  apply wordArrayAllocMem_region
  · have h192 := uadd_word_ofNat_toNat p 192
      (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
    rw [h192]
    omega
  · simp only [swapStateInitWords, ne_eq, List.cons_ne_nil, not_false_eq_true]

theorem swapReadyFrame_parts (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).contract = contract ∧
    (swapReadyFrame v a evm).immutables = immStore v := ⟨rfl, rfl⟩

theorem swapReadyFrame_state (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "state" = some (swapStateInitial a evm).value :=
  Std.HashMap.getElem?_insert_self

theorem swapReadyFrame_cache (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "cache" = some (swapCacheInitial a evm).value := by
  simp only [swapReadyFrame, swapExactFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  exact Std.HashMap.getElem?_insert_self

theorem swapReadyFrame_zero (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "zeroForOne" = some (.bool a.zeroForOne) := by
  simp only [swapReadyFrame]
  swap_exact_get

theorem swapReadyFrame_exact (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "exactInput" = some (.bool (swapExactInput a)) := by
  simp only [swapReadyFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact Std.HashMap.getElem?_insert_self

theorem swapReadyFrame_limit (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "sqrtPriceLimitX96" =
      some (.int (Int.ofNat a.priceLimit.toNat)) := by
  simp only [swapReadyFrame]
  swap_exact_get

theorem swapReadyFrame_slot (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    (swapReadyFrame v a evm).locals.get? "slot0Start" =
      some (slot0StructValue evm.accountMap evm.executionEnv) := by
  simp only [swapReadyFrame]
  swap_exact_get

theorem swapReadyFrame_growth (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (b : Bool) : (swapReadyFrame v a evm).locals.get? (feeGrowthName b) = none := by
  cases b <;> simp only [feeGrowthName, swapReadyFrame] <;> swap_exact_get

end Benchmarks.UniswapV3.Pool
