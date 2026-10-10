import Benchmarks.UniswapV4PoolManager.LeastSignificantBit
import Benchmarks.UniswapV4PoolManager.MostSignificantBitSource
import Benchmarks.UniswapV4PoolManager.ValueLocals
import Benchmarks.UniswapV4PoolManager.WordWrappingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev leastSignificantBitFunction : FunctionDecl := contract.functions[113]!
theorem leastSignificantBit_lookup : lookupCallable? contract "BitMath_leastSignificantBit" =
    some leastSignificantBitFunction.toCallable := rfl

theorem leastSignificantBit_zero {f : Frame} {evm : EVM.State}
    (hx : f.locals.get? "x" = some (.int 0)) :
    ExecFuncBody config f evm leastSignificantBitFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have he := mostSignificantBit_guard (x := ⟨0⟩) (evm := evm) hx
  simpa only [ne_eq, not_true_eq_false, decide_false] using he

theorem leastSignificantBit_body {f : Frame} {evm : EVM.State} {x : UInt256}
    (hf : f.contract = contract) (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hn : x ≠ ⟨0⟩) :
    ∃ f', ExecFuncBody config f evm leastSignificantBitFunction.body
      (.returned f' evm (some [.int (Int.ofNat (leastSignificantBit x).toNat)])) := by
  let low := lsbLowBit x
  let f1 := wordLocal f "x" low
  let f2 := wordLocal f1 "index" (lsbIndex low)
  let f3 := wordLocal f2 "r" (lsbHigh low)
  let f4 := wordLocal f3 "lowIndex" (lsbLowIndex low)
  let f5 := wordLocal f4 "low" (UInt256.byteAt (lsbLowIndex low) lsbLowTable)
  have hguard : ExecStmt config f evm leastSignificantBitFunction.body[0]! (.ok f evm) :=
    ExecStmt.requireTrue (by rw [mostSignificantBit_guard (x := x) hx, decide_eq_true hn])
  have hlow := evalWordAnd (evalLocalValue (cfg := config) (evm := evm) hx)
    (evalWordSub (x := ⟨0⟩) (a := .intLit 0) (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hx))
  rw [u256_land_comm] at hlow
  have h1 : ExecStmt config f evm leastSignificantBitFunction.body[1]! (.ok f1 evm) :=
    ExecStmt.assign hlow (assignLocalValue hx)
  have hx1 : f1.locals.get? "x" = some (.int (Int.ofNat low.toNat)) := store_get_self _ _ _
  have hindex := evalWordShl (n := 2) (b := .intLit 2) (by decide)
    (evalWordShr (n := 250) (b := .intLit 250) (by decide)
      (evalWordMul (evalLocalValue (cfg := config) (evm := evm) hx1)
        (show evalExpr? config f1 evm (.intLit 0xb6db6db6ddddddddd34d34d349249249210842108c6318c639ce739cffffffff) =
          .ok (.int (Int.ofNat lsbMultiplier.toNat)) by simp only [evalExpr?, pure]; rfl))
      (by simp only [evalExpr?, pure]; rfl))
    (by simp only [evalExpr?, pure]; rfl)
  have h2 : ExecStmt config f1 evm leastSignificantBitFunction.body[2]! (.ok f2 evm) := ExecStmt.letDecl hindex
  have hi2 : f2.locals.get? "index" = some (.int (Int.ofNat (lsbIndex low).toNat)) := store_get_self _ _ _
  have htable := evalWordShl (n := (lsbIndex low).toNat) (lsbIndex_lt hn)
    (show evalExpr? config f2 evm (.intLit 0x8040405543005266443200005020610674053026020000107506200176117077) =
      .ok (.int (Int.ofNat lsbHighTable.toNat)) by simp only [evalExpr?, pure]; rfl)
    (evalLocalValue hi2)
  simp only [u256_ofNat_toNat] at htable
  have hhigh := evalWordShl (n := 5) (b := .intLit 5) (by decide)
    (evalWordShr (n := 252) (b := .intLit 252) (by decide) htable (by simp only [evalExpr?, pure]; rfl))
    (by simp only [evalExpr?, pure]; rfl)
  have h3 : ExecStmt config f2 evm leastSignificantBitFunction.body[3]! (.ok f3 evm) := ExecStmt.letDecl hhigh
  have hx3 : f3.locals.get? "x" = some (.int (Int.ofNat low.toNat)) := by
    simp only [f3, f2, wordLocal_get, show ("r" == "x") = false from rfl,
      show ("index" == "x") = false from rfl, Bool.false_eq_true, if_false, hx1]
  have hr3 : f3.locals.get? "r" = some (.int (Int.ofNat (lsbHigh low).toNat)) := store_get_self _ _ _
  have hli := evalWordAnd
    (evalWordDiv
      (show evalExpr? config f3 evm (.intLit 0xd76453e0) = .ok (.int (Int.ofNat (⟨0xd76453e0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
      (evalWordShrWord (evalLocalValue hx3) (evalLocalValue hr3)) (lsbDenominator_ne hn))
    (show evalExpr? config f3 evm (.intLit 31) = .ok (.int (Int.ofNat (⟨31⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have h4 : ExecStmt config f3 evm leastSignificantBitFunction.body[4]! (.ok f4 evm) := ExecStmt.letDecl hli
  have hc4 : f4.contract = contract := by
    simpa only [f4, f3, f2, f1, wordLocal_contract] using hf
  have h5 : ExecStmt config f4 evm leastSignificantBitFunction.body[5]! (.ok f5 evm) :=
    wordByteCall hc4
      (show evalExpr? config f4 evm (.intLit 0x001f0d1e100c1d070f090b19131c1706010e11080a1a141802121b1503160405) =
        .ok (.int (Int.ofNat lsbLowTable.toNat)) by simp only [evalExpr?, pure]; rfl)
      (evalLocalValue (store_get_self _ _ _)) "low"
  have hr5 : f5.locals.get? "r" = some (.int (Int.ofNat (lsbHigh low).toNat)) := by
    simp only [f5, f4, wordLocal_get, show ("low" == "r") = false from rfl,
      show ("lowIndex" == "r") = false from rfl, Bool.false_eq_true, if_false, hr3]
  have hl5 : f5.locals.get? "low" = some (.int (Int.ofNat (UInt256.byteAt (lsbLowIndex low) lsbLowTable).toNat)) :=
    store_get_self _ _ _
  have hret := evalExpr_cast_int (intType := .uint ⟨8, by decide⟩)
    (evalWordOr (evalLocalValue (cfg := config) (evm := evm) hr5) (evalLocalValue hl5))
  rw [u256_lor_comm (lsbHigh low)] at hret
  change evalExpr? config f5 evm _ = .ok (.int
    (normalizeInt (.uint ⟨8, by decide⟩) (Int.ofNat (leastSignificantBit x).toNat))) at hret
  simp only [Int.ofNat_eq_natCast] at hret
  rw [normalizeInt_uint_eq_self ⟨8, by decide⟩ _ (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr (leastSignificantBit_lt_256 hn))] at hret
  exact ⟨f5, .execBlockRet (ExecBlock.consNormal hguard (ExecBlock.consNormal h1
    (ExecBlock.consNormal h2 (ExecBlock.consNormal h3 (ExecBlock.consNormal h4
      (ExecBlock.consNormal h5 (ABlock.start.returns hret)))))))⟩

theorem leastSignificantBitCall {f : Frame} {evm : EVM.State} {e : Expr} {x : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat x.toNat)))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "BitMath_leastSignificantBit" [e] retVar)
      (if x = ⟨0⟩ then .reverted else .ok (wordLocal f retVar (leastSignificantBit x)) evm) := by
  have hl : lookupCallable? f.contract "BitMath_leastSignificantBit" =
      some leastSignificantBitFunction.toCallable := by rw [hf]; exact leastSignificantBit_lookup
  by_cases hz : x = ⟨0⟩
  · rw [if_pos hz]
    apply internalCallFunctionRevert (evalExprs?_singleton he) hl rfl
    apply leastSignificantBit_zero
    simpa only [hz] using store_get_self (∅ : Store) "x" (.int (Int.ofNat x.toNat))
  · rw [if_neg hz]
    obtain ⟨f', hb⟩ := leastSignificantBit_body
      (f := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat x.toNat))})
      (evm := evm) (x := x) hf (store_get_self _ _ _) hz
    exact internalCallFunctionReturn (value := some [.int (Int.ofNat (leastSignificantBit x).toNat)])
      (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
