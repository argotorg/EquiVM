import Benchmarks.UniswapV4PoolManager.PositionFeesStoreSource
import Benchmarks.UniswapV4PoolManager.FullMath128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionFeeDifference (evm : EVM.State) (id key fee : UInt256) (second : Bool) : UInt256 :=
  UInt256.sub fee (positionFeeWord evm id key second)
def positionFeesOwed (evm : EVM.State) (id key liquidity fee : UInt256) (second : Bool) : UInt256 :=
  fullMath128Word (positionFeeDifference evm id key fee second) liquidity
def positionFeesResult (f : Frame) (evm : EVM.State) (id key liquidity fee0 fee1 : UInt256) : ExecResult :=
  if fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity then
    if fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity then
      positionFeesStoreResult f evm id key fee0 fee1
        (positionFeesOwed evm id key liquidity fee0 false) (positionFeesOwed evm id key liquidity fee1 true)
    else .reverted
  else .reverted

theorem positionFeesBody {f : Frame} {evm : EVM.State} {id key liquidity fee0 fee1 : UInt256} {old0 old1 : Value}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (positionRefValue id key))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)))
    (h1 : f.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)))
    (ho0 : f.locals.get? "feesOwed0" = some old0) (ho1 : f.locals.get? "feesOwed1" = some old1) :
    ∃ f', ExecFuncBody config f evm (positionUpdateFunction.body.drop 4)
      (positionFeesResult f' evm id key liquidity fee0 fee1) := by
  let d0 := positionFeeDifference evm id key fee0 false
  let d1 := positionFeeDifference evm id key fee1 true
  let o0 := positionFeesOwed evm id key liquidity fee0 false
  let o1 := positionFeesOwed evm id key liquidity fee1 true
  let f1 := wordLocal f "__c1" o0
  let f2 := wordLocal f1 "feesOwed0" o0
  let f3 := wordLocal f2 "__c2" o1
  let f4 := wordLocal f3 "feesOwed1" o1
  have hcall0 := fullMath128Call (f := f) (evm := evm) hf
    (evalWordSub (evalLocalValue h0) (positionFee_read hs false)) (evalLocalValue hl)
    (show evalExpr? config f evm (.intLit (2^128)) = .ok (.int (Int.ofNat fullMathQ128.toNat)) by
      simp only [evalExpr?, pure]; rfl) "__c1"
  by_cases hf0 : fullMath128Fits d0 liquidity
  · change fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity at hf0
    change ExecStmt config f evm positionUpdateFunction.body[4]!
      (if fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity then .ok f1 evm else .reverted) at hcall0
    rw [if_pos hf0] at hcall0
    have hassign0 : ExecStmt config f1 evm positionUpdateFunction.body[5]! (.ok f2 evm) :=
      ExecStmt.assign wordLocal_eval (assignLocalValue (by
        simpa only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte] using ho0))
    have hs2 : f2.locals.get? "self" = some (positionRefValue id key) := by
      simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
    have hl2 : f2.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) := by
      simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hl]
    have h12 : f2.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)) := by
      simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, h1]
    have hcall1 := fullMath128Call (f := f2) (evm := evm) hf
      (evalWordSub (evalLocalValue h12) (positionFee_read hs2 true)) (evalLocalValue hl2)
      (show evalExpr? config f2 evm (.intLit (2^128)) = .ok (.int (Int.ofNat fullMathQ128.toNat)) by
        simp only [evalExpr?, pure]; rfl) "__c2"
    by_cases hf1 : fullMath128Fits d1 liquidity
    · change fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity at hf1
      change ExecStmt config f2 evm positionUpdateFunction.body[6]!
        (if fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity then .ok f3 evm else .reverted) at hcall1
      rw [if_pos hf1] at hcall1
      have hassign1 : ExecStmt config f3 evm positionUpdateFunction.body[7]! (.ok f4 evm) :=
        ExecStmt.assign wordLocal_eval (assignLocalValue (by
          simpa only [f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte] using ho1))
      have hs4 : f4.locals.get? "self" = some (positionRefValue id key) := by
        simp only [f4, f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hs2]
      have h04 : f4.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)) := by
        simp only [f4, f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, h0]
      have h14 : f4.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)) := by
        simp only [f4, f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, h12]
      have ho04 : f4.locals.get? "feesOwed0" = some (.int (Int.ofNat o0.toNat)) := by
        simp only [f4, f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
      have hstores := positionFeesStoreBody (f := f4) (evm := evm) hs4 h04 h14 ho04 (store_get_self _ _ _)
      refine ⟨f4, ?_⟩
      simp only [positionFeesResult, if_pos hf0, if_pos hf1]
      exact execFuncBody_prepend (ExecBlock.consNormal hcall0 (ExecBlock.consNormal hassign0
        (ExecBlock.consNormal hcall1 (execBlock_singleton hassign1)))) hstores
    · change ¬fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity at hf1
      change ExecStmt config f2 evm positionUpdateFunction.body[6]!
        (if fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity then .ok f3 evm else .reverted) at hcall1
      rw [if_neg hf1] at hcall1
      refine ⟨f2, ?_⟩
      simp only [positionFeesResult, if_pos hf0, if_neg hf1]
      exact .execBlockRevert (ExecBlock.consNormal hcall0 (ExecBlock.consNormal hassign0
        (ExecBlock.consRevert hcall1)))
  · change ¬fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity at hf0
    change ExecStmt config f evm positionUpdateFunction.body[4]!
      (if fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity then .ok f1 evm else .reverted) at hcall0
    rw [if_neg hf0] at hcall0
    refine ⟨f, ?_⟩
    simp only [positionFeesResult, if_neg hf0]
    exact .execBlockRevert (ExecBlock.consRevert hcall0)

end Benchmarks.UniswapV4PoolManager
