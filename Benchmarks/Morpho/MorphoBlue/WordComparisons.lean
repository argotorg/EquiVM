import Benchmarks.Morpho.MorphoBlue.AccruePublicSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: inequality of two machine-word integers in any source frame.
theorem evalWordNeWord {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg frame evm (.binary .ne ex ey) = .ok (.bool (decide (x ≠ y))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [pure, bind, EvalResult.bind, evalBinaryOp?]
  have hbeq : (Value.int (Int.ofNat x.toNat) == Value.int (Int.ofNat y.toNat)) = decide (x = y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, Int.ofNat.injEq, decide_eq_true_eq]
    exact ⟨u256_inj, fun h => congrArg UInt256.toNat h⟩
  rw [hbeq, decide_not]

-- LIBRARY CANDIDATE: equality of two machine-word integers in any source frame.
theorem evalWordEqWord {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg frame evm (.binary .eq ex ey) = .ok (.bool (decide (x = y))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.ofNat.injEq, decide_eq_true_eq]
  exact ⟨u256_inj, fun h ↦ congrArg UInt256.toNat h⟩


-- LIBRARY CANDIDATE: a canonical address's nonzero guard agrees with its word representation.
theorem evalCanonicalAddressNeZero {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr}
    {word : UInt256} (hc : word.toNat < EVM.addressModulus)
    (he : evalExpr? cfg frame evm expr = .ok (.address (AccountAddress.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.binary .ne expr (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (word ≠ ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), he]
  simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption,
    show ¬ (0 : Int) < 0 from by decide, ↓reduceIte, evalBinaryOp?]
  change EvalResult.ok (Value.bool (!(Value.address (AccountAddress.ofNat word.toNat) ==
    Value.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)))) = _
  rw [canonicalAddress_beq _ _ hc (by decide), decide_not]

end Benchmarks.Morpho.MorphoBlue
