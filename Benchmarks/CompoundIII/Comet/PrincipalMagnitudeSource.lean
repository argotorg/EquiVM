import Benchmarks.CompoundIII.Comet.PrincipalMagnitudeModel
import Benchmarks.CompoundIII.Comet.CheckedAddSubSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem principalMagnitudeExpr_ok (borrow : Bool) (cfg : Config) (frame : Frame) (evm : EVM.State)
    (index present : UInt256)
    (hp : evalExpr? cfg frame evm (.var "presentValue_") = .ok (.int present.toNat))
    (hi : evalExpr? cfg frame evm (.var (principalMagnitudeIndexName borrow)) =
      .ok (.int index.toNat)) (hf : PrincipalMagnitudeEvalFits borrow index present) :
    evalExpr? cfg frame evm (principalMagnitudeExpr borrow) =
      .ok (.int (principalMagnitudeWord borrow index present).toNat) := by
  have hm := checkedMulSourceOk (a := present) (b := ⟨1000000000000000⟩) hp
    (show evalExpr? cfg frame evm (.intLit 1000000000000000) =
      .ok (.int (Int.ofNat (⟨1000000000000000⟩ : UInt256).toNat)) from by
        simp only [evalExpr?, pure]; rfl) hf.1
  change evalExpr? cfg frame evm principalMagnitudeProductExpr =
    .ok (.int (Int.ofNat (principalMagnitudeProduct present).toNat)) at hm
  apply divSourceOk (a := principalMagnitudeNumerator borrow index present) (b := index) ?_ hi hf.2.2
  cases borrow
  · exact hm
  · have hb := hf.2.1 rfl
    exact checkedAddSubOneSourceOk hm hi hb.1 hb.2

theorem principalMagnitudeExpr_revert (borrow : Bool) (cfg : Config) (frame : Frame) (evm : EVM.State)
    (index present : UInt256)
    (hp : evalExpr? cfg frame evm (.var "presentValue_") = .ok (.int present.toNat))
    (hi : evalExpr? cfg frame evm (.var (principalMagnitudeIndexName borrow)) =
      .ok (.int index.toNat)) (hf : ¬ PrincipalMagnitudeEvalFits borrow index present) :
    evalExpr? cfg frame evm (principalMagnitudeExpr borrow) = .revert := by
  have hscale : evalExpr? cfg frame evm (.intLit 1000000000000000) =
      .ok (.int (Int.ofNat (⟨1000000000000000⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  by_cases hprod : present.toNat * 1000000000000000 < UInt256.size
  · have hm := checkedMulSourceOk (a := present) (b := ⟨1000000000000000⟩) hp hscale hprod
    change evalExpr? cfg frame evm principalMagnitudeProductExpr =
      .ok (.int (Int.ofNat (principalMagnitudeProduct present).toNat)) at hm
    cases borrow
    · have hz : index = ⟨0⟩ := by
        by_contra hn; exact hf ⟨hprod, (by intro hh; cases hh), hn⟩
      have hi0 : evalExpr? cfg frame evm (.var (principalMagnitudeIndexName false)) =
          .ok (.int 0) := by rw [hi, hz]; rfl
      exact divSourceZero hm hi0
    · by_cases hadd : (principalMagnitudeProduct present).toNat + index.toNat < UInt256.size
      · by_cases hsub : 1 ≤ (principalMagnitudeSum index present).toNat
        · have hs := checkedAddSubOneSourceOk hm hi hadd hsub
          have hz : index = ⟨0⟩ := by
            by_contra hn; exact hf ⟨hprod, fun _ ↦ ⟨hadd, hsub⟩, hn⟩
          have hi0 : evalExpr? cfg frame evm (.var (principalMagnitudeIndexName true)) =
              .ok (.int 0) := by rw [hi, hz]; rfl
          exact divSourceZero hs hi0
        · have hs := checkedAddSubOneSourceUnderflow hm hi hadd (by
            change (principalMagnitudeSum index present).toNat < 1; omega)
          change evalExpr? cfg frame evm (principalMagnitudeNumeratorExpr true) = .revert at hs
          change evalExpr? cfg frame evm (.binary .div _ _) = .revert
          simp only [evalExpr?, hs, bind, EvalResult.bind]
      · have ha := checkedAddSourceOverflow (a := principalMagnitudeProduct present)
          (b := index) hm hi (Nat.le_of_not_lt hadd)
        simp only [principalMagnitudeExpr, principalMagnitudeNumeratorExpr, if_true,
          evalExpr?, ha, bind, EvalResult.bind]
  · have hm := checkedMulSourceOverflow (a := present) (b := ⟨1000000000000000⟩) hp hscale (by
      change UInt256.size ≤ present.toNat * 1000000000000000; omega)
    change evalExpr? cfg frame evm principalMagnitudeProductExpr = .revert at hm
    cases borrow <;> simp only [principalMagnitudeExpr, principalMagnitudeNumeratorExpr,
      Bool.false_eq_true, if_false, if_true, evalExpr?, hm, bind, EvalResult.bind]

theorem principalMagnitude_source (borrow : Bool) (evm : EVM.State) (imms : Store)
    (index present : UInt256) :
    let frame := principalMagnitudeEntry imms borrow index present
    if PrincipalMagnitudeFits borrow index present then
      ∃ final, ExecFuncBody config frame evm (principalMagnitudeCallable borrow).body
        (.returned final evm (some [.int (principalMagnitudeWord borrow index present).toNat]))
    else ExecFuncBody config frame evm (principalMagnitudeCallable borrow).body .reverted := by
  dsimp only
  let frame := principalMagnitudeEntry imms borrow index present
  have hp : evalExpr? config frame evm (.var "presentValue_") = .ok (.int present.toNat) := by
    cases borrow <;> simp only [evalExpr?, frame, principalMagnitudeEntry,
      principalMagnitudeIndexName, Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption] <;> rfl
  have hi : evalExpr? config frame evm (.var (principalMagnitudeIndexName borrow)) =
      .ok (.int index.toNat) := by
    simp only [evalExpr?, frame, principalMagnitudeEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_self_eq_true, if_true, EvalResult.ofOption]
  by_cases he : PrincipalMagnitudeEvalFits borrow index present
  · have hx := principalMagnitudeExpr_ok borrow config frame evm index present hp hi he
    have hc := safeUint_call ⟨104, by decide⟩ "safe104" safe104Callable_lookup frame evm
      (principalMagnitudeWord borrow index present) (principalMagnitudeExpr borrow) "__c0" rfl hx
    by_cases hn : (principalMagnitudeWord borrow index present).toNat < 2^104
    · rw [if_pos hn] at hc
      rw [if_pos ⟨he, hn⟩]
      refine ⟨{ frame with
        locals := frame.locals.insert "__c0" (.int (principalMagnitudeWord borrow index present).toNat) },
        ExecFuncBody.execBlockRet (ExecBlock.consNormal hc ?_)⟩
      apply ExecBlock.consReturn
      apply ExecStmt.return
      simp only [evalExprs?, evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption, pure, bind, EvalResult.bind]; rfl
    · rw [if_neg hn] at hc
      rw [if_neg (fun h ↦ hn h.2)]
      exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert hc)
  · rw [if_neg (fun h ↦ he h.1)]
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply ExecStmt.internalCallArgsRevert
    change evalExprs? config frame evm [principalMagnitudeExpr borrow] = .revert
    simp only [evalExprs?, principalMagnitudeExpr_revert borrow config frame evm index present hp hi he,
      bind, EvalResult.bind]

theorem principalMagnitude_call (borrow : Bool) (frame : Frame) (evm : EVM.State)
    (index present : UInt256) (indexExpr presentExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract)
    (hi : evalExpr? config frame evm indexExpr = .ok (.int index.toNat))
    (hp : evalExpr? config frame evm presentExpr = .ok (.int present.toNat)) :
    ExecStmt config frame evm (.internalCall (principalMagnitudeName borrow) [indexExpr, presentExpr] ret)
      (if PrincipalMagnitudeFits borrow index present then
        .ok { frame with
          locals := frame.locals.insert ret (.int (principalMagnitudeWord borrow index present).toNat) }
          evm else .reverted) := by
  have hb := principalMagnitude_source borrow evm frame.immutables index present
  dsimp only at hb
  split_ifs with hn
  · rw [if_pos hn] at hb
    obtain ⟨final, hb⟩ := hb
    exact ExecStmt.internalCallReturn (callee := principalMagnitudeCallable borrow)
      (cfg := config) (solm := frame) (evm := evm) (args := [indexExpr, presentExpr])
      (locals := (principalMagnitudeEntry frame.immutables borrow index present).locals)
      (argVals := [.int index.toNat, .int present.toNat])
      (by simp only [evalExprs?, hi, hp, pure, bind, EvalResult.bind])
      (by rw [hc]; exact principalMagnitudeCallable_lookup borrow) rfl
      (by simpa only [hc] using hb)
  · rw [if_neg hn] at hb
    exact ExecStmt.internalCallRevert (callee := principalMagnitudeCallable borrow)
      (cfg := config) (solm := frame) (evm := evm) (args := [indexExpr, presentExpr])
      (locals := (principalMagnitudeEntry frame.immutables borrow index present).locals)
      (argVals := [.int index.toNat, .int present.toNat])
      (by simp only [evalExprs?, hi, hp, pure, bind, EvalResult.bind])
      (by rw [hc]; exact principalMagnitudeCallable_lookup borrow) rfl
      (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
