import Benchmarks.UniswapV3.Pool.SwapGuardsSource
import Benchmarks.UniswapV3.Pool.BlockTimestamp
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SwapCacheData where
  feeProtocol : UInt256
  liquidityStart : UInt256
  blockTimestamp : UInt256
  tickCumulative : Int
  secondsPerLiquidity : UInt256
  computedLatestObservation : Bool

def SwapCacheData.value (c : SwapCacheData) : Value :=
  .struct "SwapCache" [
    ("liquidityStart", .int (Int.ofNat c.liquidityStart.toNat)),
    ("blockTimestamp", .int (Int.ofNat c.blockTimestamp.toNat)),
    ("feeProtocol", .int (Int.ofNat c.feeProtocol.toNat)),
    ("secondsPerLiquidityCumulativeX128", .int (Int.ofNat c.secondsPerLiquidity.toNat)),
    ("tickCumulative", .int c.tickCumulative),
    ("computedLatestObservation", .bool c.computedLatestObservation)]

def SwapCacheData.words (c : SwapCacheData) : List UInt256 :=
  [c.feeProtocol, c.liquidityStart, c.blockTimestamp, EVM.wordOfInt c.tickCumulative,
    c.secondsPerLiquidity, c.computedLatestObservation.toUInt256]

def swapCacheInitial (a : SwapArgs) (evm : EVM.State) : SwapCacheData :=
  {feeProtocol := poolProtocolDivisor (!a.zeroForOne) evm.accountMap evm.executionEnv,
    liquidityStart := poolLiquidityWord (storeSlot0Unlocked evm false).accountMap evm.executionEnv,
    blockTimestamp := blockTimestampWord evm.executionEnv,
    tickCumulative := 0, secondsPerLiquidity := ⟨0⟩, computedLatestObservation := false}

def swapTimeFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (swapSlot0Frame v a evm) "__c1"
    (some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])

def swapCachedFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) : Frame :=
  {swapTimeFrame v a evm with
    locals := (swapTimeFrame v a evm).locals.insert "cache" (swapCacheInitial a evm).value}

def swapCacheFeeExpr : Expr :=
  .ite (.var "zeroForOne")
    (.binary .mod (.field (.var "slot0Start") "feeProtocol") (.intLit 16))
    (.binary (.shr (.uint ⟨8, by decide⟩))
      (.field (.var "slot0Start") "feeProtocol") (.intLit 4))

def swapCacheExpr : Expr :=
  .structLit "SwapCache" [
    ("liquidityStart", .storage ⟨"liquidity", []⟩),
    ("blockTimestamp", .var "__c1"), ("feeProtocol", swapCacheFeeExpr),
    ("secondsPerLiquidityCumulativeX128", .intLit 0),
    ("tickCumulative", .intLit 0), ("computedLatestObservation", .boolLit false)]

macro "swap_time_get" : tactic =>
  `(tactic| (simp only [swapTimeFrame, swapSlot0Frame, swapDelegateFrame, swapInitFrame,
    poolAmountsFrame, swapFrame, swapLocals, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem swapTimestampSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    ExecStmt config (swapSlot0Frame v a evm) (storeSlot0Unlocked evm false)
      (.internalCall "_blockTimestamp" [] "__c1")
      (.ok (swapTimeFrame v a evm) (storeSlot0Unlocked evm false)) := by
  have hret := blockTimestampReturns (immStore v) (storeSlot0Unlocked evm false)
  rw [storeSlot0Unlocked_executionEnv] at hret
  exact internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
    (calleeSolm := {contract := contract, locals := ∅, immutables := immStore v})
    (value := some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])
    (by rfl) blockTimestampLookup rfl hret

theorem evalSwapCacheFee (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm evm' : EVM.State) :
    evalExpr? config (swapTimeFrame v a evm) evm' swapCacheFeeExpr =
      .ok (.int (Int.ofNat (swapCacheInitial a evm).feeProtocol.toNat)) := by
  have hz : evalExpr? config (swapTimeFrame v a evm) evm' (.var "zeroForOne") =
      .ok (.bool a.zeroForOne) := evalExpr_var_get (by swap_time_get)
  have hs : evalExpr? config (swapTimeFrame v a evm) evm' (.var "slot0Start") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by swap_time_get)
  have hf := evalExpr_structField (name := "feeProtocol") hs rfl
  rw [swapCacheFeeExpr, evalExpr?, hz]
  cases hdir : a.zeroForOne
  · have hsmall : (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat < 256 :=
      u256LandMaskToNatLtOfToNat (bits := 8) _ _ (by decide)
    have hn : normalizeInt (.uint ⟨8, by decide⟩)
        (Int.ofNat (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat) =
        Int.ofNat (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat :=
      normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hsmall)
    have he := evalExpr_uintShiftRight ⟨8, by decide⟩ _ 4 hf (by decide)
    simp only [bind, EvalResult.bind]
    simpa only [swapCacheInitial, hdir, Bool.not_false, poolProtocolDivisor_toNat,
      if_true, hn, Int.natCast_ediv] using he
  · have h16 : evalExpr? config (swapTimeFrame v a evm) evm' (.intLit 16) =
        .ok (.int (Int.ofNat (⟨16⟩ : UInt256).toNat)) := by
      simp only [evalExpr?, pure]; rfl
    have he := evalExpr_word_mod hf h16 (by decide)
    simp only [bind, EvalResult.bind]
    simpa only [swapCacheInitial, hdir, Bool.not_true, poolProtocolDivisor_toNat,
      Bool.false_eq_true, if_false, umod_toNat_of_ne_zero _ (⟨16⟩ : UInt256) (by decide),
      show (⟨16⟩ : UInt256).toNat = 16 from rfl] using he

theorem evalSwapCache (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapTimeFrame v a evm) (storeSlot0Unlocked evm false) swapCacheExpr =
      .ok (swapCacheInitial a evm).value := by
  have hli := evalLiquidity (swapTimeFrame v a evm).locals (immStore v)
    (storeSlot0Unlocked evm false) (by swap_time_get)
  have ht : evalExpr? config (swapTimeFrame v a evm) (storeSlot0Unlocked evm false) (.var "__c1") =
      .ok (.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)) :=
    evalExpr_var_get (by swap_time_get)
  have hf := evalSwapCacheFee v a evm (storeSlot0Unlocked evm false)
  change evalExpr? config (swapTimeFrame v a evm) _ _ = _ at hli
  simp only [storeSlot0Unlocked_executionEnv] at hli
  simp only [swapCacheExpr, evalExpr?, evalStructFields?, hli, ht, hf,
    bind, EvalResult.bind, pure, swapCacheInitial, SwapCacheData.value, poolLiquidityWord]
  rfl

theorem swapCacheSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    ExecBlock config (swapSlot0Frame v a evm) (storeSlot0Unlocked evm false)
      ((swapTransition.body.drop 9).take 2)
      (.ok (swapCachedFrame v a evm) (storeSlot0Unlocked evm false)) := by
  exact ExecBlock.consNormal (swapTimestampSource v a evm)
    (ExecBlock.consNormal (ExecStmt.letDecl (evalSwapCache v a evm)) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
