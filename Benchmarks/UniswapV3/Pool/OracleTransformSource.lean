import Benchmarks.UniswapV3.Pool.ModularWords
import Benchmarks.UniswapV3.Pool.PackedStorage
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure OracleObservation where
  timestamp : UInt256
  tickCumulative : Int
  secondsPerLiquidity : UInt256
  initialized : Bool

def OracleObservation.value (last : OracleObservation) : Value :=
  .struct "Observation" [
    ("blockTimestamp", .int (Int.ofNat last.timestamp.toNat)),
    ("tickCumulative", .int last.tickCumulative),
    ("secondsPerLiquidityCumulativeX128", .int (Int.ofNat last.secondsPerLiquidity.toNat)),
    ("initialized", .bool last.initialized)]

def oracleDelta (time previous : UInt256) : UInt256 :=
  UInt256.land (UInt256.sub time previous) (UInt256.ofNat (2 ^ 32 - 1))

theorem oracleDelta_lt (time previous : UInt256) : (oracleDelta time previous).toNat < 2 ^ 32 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

def oracleLiquidityDenominator (liquidity : UInt256) : UInt256 :=
  if 0 < liquidity.toNat then liquidity else ⟨1⟩

theorem oracleLiquidityDenominator_pos (liquidity : UInt256) :
    0 < (oracleLiquidityDenominator liquidity).toNat := by
  unfold oracleLiquidityDenominator
  split
  · assumption
  · decide

def oracleTransformed (last : OracleObservation) (time : UInt256) (tick : Int)
    (liquidity : UInt256) : OracleObservation :=
  { timestamp := time
    tickCumulative := normalizeInt (.sint ⟨56, by decide⟩)
      (last.tickCumulative + tick * Int.ofNat (oracleDelta time last.timestamp).toNat)
    secondsPerLiquidity := UInt256.land
      (last.secondsPerLiquidity + UInt256.div
        (UInt256.shiftLeft (oracleDelta time last.timestamp) ⟨128⟩)
        (oracleLiquidityDenominator liquidity)) (UInt256.ofNat (2 ^ 160 - 1))
    initialized := true }

theorem oracleDelta_source (time previous : UInt256) :
    normalizeInt (.uint ⟨32, by decide⟩) (Int.ofNat time.toNat - Int.ofNat previous.toNat) =
      Int.ofNat (oracleDelta time previous).toNat := by
  rw [normalizeUIntInt_mask ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
  rfl

theorem oracleDelta_shift (time previous : UInt256) :
    (UInt256.shiftLeft (oracleDelta time previous) ⟨128⟩).toNat =
      (oracleDelta time previous).toNat * 2 ^ 128 := by
  exact shiftLeft_toNat_of_noOverflow _ _ (by decide) (by
    have h := oracleDelta_lt time previous
    change _ * 2 ^ 128 < 2 ^ 256
    omega)

theorem oracleTransformed_tick_word (last : OracleObservation) (time : UInt256)
    (tick : Int) (liquidity : UInt256) :
    EVM.wordOfInt (oracleTransformed last time tick liquidity).tickCumulative =
      UInt256.signextend (UInt256.ofNat 6)
        (EVM.wordOfInt last.tickCumulative +
          UInt256.mul (EVM.wordOfInt tick) (oracleDelta time last.timestamp)) := by
  have h := signextend_wordOfInt ⟨56, by decide⟩ (UInt256.ofNat 6)
    (last.tickCumulative + tick * Int.ofNat (oracleDelta time last.timestamp).toNat)
    (by decide) (by decide)
  rw [wordOfInt_add, wordOfInt_mul, wordOfInt_ofNat_toNat] at h
  exact h.symm

def oracleTransformFunction : FunctionDecl := contract.functions[28]!

theorem oracleTransformLookup :
    lookupCallable? contract "Oracle_transform" = some oracleTransformFunction.toCallable := rfl

def oracleTransformLocals (last : OracleObservation) (time : UInt256)
    (tick : Int) (liquidity : UInt256) : Store :=
  ((((∅ : Store).insert "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "tick" (.int tick)).insert
    "blockTimestamp" (.int (Int.ofNat time.toNat))).insert "last" last.value

def oracleTransformFrame (imms : Store) (last : OracleObservation) (time : UInt256)
    (tick : Int) (liquidity : UInt256) : Frame :=
  {contract := contract, locals := oracleTransformLocals last time tick liquidity, immutables := imms}

theorem oracleTransformBind (last : OracleObservation) (time : UInt256)
    (tick : Int) (liquidity : UInt256) :
    bindParams? oracleTransformFunction.params
      [last.value, .int (Int.ofNat time.toNat), .int tick, .int (Int.ofNat liquidity.toNat)] =
      some (oracleTransformLocals last time tick liquidity) := rfl

def oracleTransformDeltaFrame (imms : Store) (last : OracleObservation) (time : UInt256)
    (tick : Int) (liquidity : UInt256) : Frame :=
  {oracleTransformFrame imms last time tick liquidity with
    locals := (oracleTransformLocals last time tick liquidity).insert "delta"
      (.int (Int.ofNat (oracleDelta time last.timestamp).toNat))}

theorem evalOracleTransformDelta (imms : Store) (evm : EVM.State) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256) :
    evalExpr? config (oracleTransformFrame imms last time tick liquidity) evm
      (.cast (.binary .sub (.var "blockTimestamp") (.field (.var "last") "blockTimestamp"))
        (.elem (.int (.uint ⟨32, by decide⟩)))) =
      .ok (.int (Int.ofNat (oracleDelta time last.timestamp).toNat)) := by
  simp [evalExpr?, oracleTransformFrame, oracleTransformLocals, OracleObservation.value,
    Std.HashMap.getElem_insert, lookupField?, lookupAssoc, EvalResult.ofOption,
    castValue?, evalBinaryOp?, bind, EvalResult.bind]
  exact oracleDelta_source time last.timestamp


def oracleTransformResultExpr : Expr :=
  .structLit "Observation" [
    ("blockTimestamp", .var "blockTimestamp"),
    ("tickCumulative", .cast
      (.binary .add (.field (.var "last") "tickCumulative")
        (.cast (.binary .mul
          (.cast (.var "tick") (.elem (.int (.sint ⟨56, by decide⟩)))) (.var "delta"))
          (.elem (.int (.sint ⟨56, by decide⟩)))))
      (.elem (.int (.sint ⟨56, by decide⟩)))),
    ("secondsPerLiquidityCumulativeX128", .cast
      (.binary .add (.field (.var "last") "secondsPerLiquidityCumulativeX128")
        (.binary .div
          (.binary (.shl (.uint ⟨160, by decide⟩))
            (.cast (.var "delta") (.elem (.int (.uint ⟨160, by decide⟩)))) (.intLit 128))
          (.ite (.binary .gt (.var "liquidity") (.intLit 0)) (.var "liquidity") (.intLit 1))))
      (.elem (.int (.uint ⟨160, by decide⟩)))),
    ("initialized", .boolLit true)]

theorem evalOracleTransformResult (imms : Store) (evm : EVM.State) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    evalExpr? config (oracleTransformDeltaFrame imms last time tick liquidity) evm
      oracleTransformResultExpr = .ok (oracleTransformed last time tick liquidity).value := by
  let delta := oracleDelta time last.timestamp
  have hdlt : delta.toNat < 2 ^ 32 := oracleDelta_lt _ _
  have ht : normalizeInt (.sint ⟨56, by decide⟩) tick = tick :=
    normalizeSint_eq_self _ tick (by change -(2 ^ 55 : Int) ≤ tick; omega)
      (by change tick < (2 ^ 55 : Int); omega)
  have hd : normalizeInt (.uint ⟨160, by decide⟩) (Int.ofNat delta.toNat) = Int.ofNat delta.toNat :=
    normalizeInt_uint_eq_self ⟨160, by decide⟩ _ (Int.natCast_nonneg _) (by
      have h : delta.toNat < EVM.twoPow 160 := by change delta.toNat < 2 ^ 160; omega
      exact Int.ofNat_lt.mpr h)
  have hdwide : delta.toNat * 2 ^ 128 < 2 ^ 160 := by omega
  have hds : normalizeInt (.uint ⟨160, by decide⟩)
      (Int.ofNat delta.toNat * Int.ofNat (EVM.twoPow 128)) =
      Int.ofNat delta.toNat * Int.ofNat (EVM.twoPow 128) :=
    normalizeInt_uint_eq_self ⟨160, by decide⟩ _
      (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (by
        simpa only [Int.ofNat_eq_natCast, EVM.twoPow, Nat.cast_pow, Nat.cast_ofNat] using
          (show (delta.toNat : Int) * (2 ^ 128 : Int) < 2 ^ 160 by exact_mod_cast hdwide))
  have hsec : normalizeInt (.uint ⟨160, by decide⟩)
      (Int.ofNat last.secondsPerLiquidity.toNat +
        Int.ofNat (UInt256.div (UInt256.shiftLeft delta ⟨128⟩)
          (oracleLiquidityDenominator liquidity)).toNat) =
      Int.ofNat (oracleTransformed last time tick liquidity).secondsPerLiquidity.toNat := by
    rw [normalizeUIntInt_mask ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
      wordOfInt_add, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
    rfl
  have hquot : Int.ofNat (UInt256.div (UInt256.shiftLeft delta ⟨128⟩)
      (oracleLiquidityDenominator liquidity)).toNat =
      (Int.ofNat delta.toNat * Int.ofNat (EVM.twoPow 128)) /
        Int.ofNat (oracleLiquidityDenominator liquidity).toNat := by
    rw [udiv_toNat, oracleDelta_shift]
    simp only [Int.ofNat_eq_natCast, Int.natCast_ediv, Int.natCast_mul]
    rfl
  rw [hquot] at hsec
  change normalizeInt (.uint ⟨160, by decide⟩)
    (Int.ofNat last.secondsPerLiquidity.toNat +
      Int.ofNat delta.toNat * Int.ofNat (EVM.twoPow 128) /
        Int.ofNat (oracleLiquidityDenominator liquidity).toNat) =
    Int.ofNat (UInt256.land
      (last.secondsPerLiquidity + UInt256.div (UInt256.shiftLeft delta ⟨128⟩)
        (oracleLiquidityDenominator liquidity)) (UInt256.ofNat (2 ^ 160 - 1))).toNat at hsec
  simp only [Int.ofNat_eq_natCast] at hd hds hsec
  dsimp only [delta] at hd hds hsec
  by_cases hl : 0 < liquidity.toNat
  · have hn : liquidity.toNat ≠ 0 := by omega
    simp only [oracleLiquidityDenominator, if_pos hl] at hsec
    simp [oracleTransformResultExpr, evalExpr?, evalStructFields?, oracleTransformDeltaFrame,
      oracleTransformFrame, oracleTransformLocals, OracleObservation.value,
      Std.HashMap.getElem_insert, lookupField?, lookupAssoc, EvalResult.ofOption,
      castValue?, evalBinaryOp?, IntType.bitWidth, bind, EvalResult.bind, pure, hn, ht, hd,
      hds, normalizeInt_add_right, oracleTransformed, oracleLiquidityDenominator, hl]
    simpa only [show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.cast_one, Int.ediv_one] using hsec
  · have hz : liquidity.toNat = 0 := by omega
    simp only [oracleLiquidityDenominator, if_neg hl] at hsec
    simp [oracleTransformResultExpr, evalExpr?, evalStructFields?, oracleTransformDeltaFrame,
      oracleTransformFrame, oracleTransformLocals, OracleObservation.value,
      Std.HashMap.getElem_insert, lookupField?, lookupAssoc, EvalResult.ofOption,
      castValue?, evalBinaryOp?, IntType.bitWidth, bind, EvalResult.bind, pure, hz, ht, hd,
      hds, normalizeInt_add_right, oracleTransformed, oracleLiquidityDenominator]
    simpa only [show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.cast_one, Int.ediv_one] using hsec


theorem oracleTransformReturns (imms : Store) (evm : EVM.State) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    ExecFuncBody config (oracleTransformFrame imms last time tick liquidity) evm
      oracleTransformFunction.body
      (.returned (oracleTransformDeltaFrame imms last time tick liquidity) evm
        (some [(oracleTransformed last time tick liquidity).value])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalOracleTransformDelta imms evm last time tick liquidity)) ?_
  apply ABlock.start.returns
  exact evalOracleTransformResult imms evm last time tick liquidity htick

end Benchmarks.UniswapV3.Pool
