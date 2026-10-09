import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES checkedAddSubOneSourceOk to arbitrary unsigned widths and subtrahends.
theorem checkedNarrowAddSubSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y z : UInt256} {a b c : Expr} (width : BitWidth) (hw : width.val ≤ 256)
    (hx : evalExpr? cfg frame evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm b = .ok (.int (Int.ofNat y.toNat)))
    (hz : evalExpr? cfg frame evm c = .ok (.int (Int.ofNat z.toNat))) :
    evalExpr? cfg frame evm (.inRange (.uint width) (.binary .sub
      (.inRange (.uint width) (.binary .add a b)) c)) =
      if x.toNat + y.toNat < 2^width.val ∧ z.toNat ≤ (x + y).toNat then
        .ok (.int (Int.ofNat (UInt256.sub (x + y) z).toNat)) else .revert := by
  by_cases ha : x.toNat + y.toNat < 2^width.val
  · have hadd := checkedNarrowAddSourceOk width hw hx hy ha
    have hn : (x + y).toNat < 2^width.val := by
      have hsize : x.toNat + y.toNat < UInt256.size :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hw)
      rw [uadd_toNat, Nat.mod_eq_of_lt hsize]
      exact ha
    by_cases hs : z.toNat ≤ (x + y).toNat
    · rw [if_pos ⟨ha, hs⟩]
      exact checkedNarrowSubSourceOk width hadd hz hn hs
    · rw [if_neg (fun h ↦ hs h.2)]
      exact checkedNarrowSubSourceUnderflow width hadd hz (Nat.lt_of_not_ge hs)
  · rw [if_neg (fun h ↦ ha h.1)]
    have hadd := uintRangeSourceOverflow width (naturalAddSource hx hy) (Nat.le_of_not_gt ha)
    simp only [evalExpr?, hadd, bind, EvalResult.bind]

-- LIBRARY CANDIDATE: compose the two checked operations used in rounded-up division.
theorem checkedAddSubOneSourceOk {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : UInt256} {a b : Expr}
    (hx : evalExpr? cfg frame evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm b = .ok (.int (Int.ofNat y.toNat)))
    (hf : x.toNat + y.toNat < UInt256.size) (hb : 1 ≤ (x + y).toNat) :
    evalExpr? cfg frame evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .sub
        (.inRange (.uint ⟨256, by decide⟩) (.binary .add a b)) (.intLit 1))) =
      .ok (.int (Int.ofNat (UInt256.sub (x + y) ⟨1⟩).toNat)) := by
  have ha := checkedAddSourceOk hx hy hf
  have hs := subSourceOk ha
    (show evalExpr? cfg frame evm (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) from by simp only [evalExpr?, pure]; rfl) hb
  exact uint256RangeSourceOk hs (UInt256.sub (x + y) ⟨1⟩).val.isLt

theorem checkedAddSubOneSourceUnderflow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : UInt256} {a b : Expr}
    (hx : evalExpr? cfg frame evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm b = .ok (.int (Int.ofNat y.toNat)))
    (hf : x.toNat + y.toNat < UInt256.size) (hb : (x + y).toNat < 1) :
    evalExpr? cfg frame evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .sub
        (.inRange (.uint ⟨256, by decide⟩) (.binary .add a b)) (.intLit 1))) = .revert := by
  exact checkedNarrowSubSourceUnderflow ⟨256, by decide⟩ (checkedAddSourceOk hx hy hf)
    (show evalExpr? cfg frame evm (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) from by simp only [evalExpr?, pure]; rfl) hb

end Benchmarks.CompoundIII.Comet
