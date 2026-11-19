import Benchmarks.Midnight.WordBitSource
import Benchmarks.Midnight.CollateralLoopMemory
import Reasoning.VyperDispatch

/-! Source semantics of the bitmap helpers used by collateral health checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev bitmapMsbFunction : FunctionDecl := contract.functions[19]!
abbrev bitmapClearFunction : FunctionDecl := contract.functions[18]!

def bitmapMsbLoop : Stmt := .while (.binary .ne (.var "bits") (.intLit 0))
  [.assign .localVar { base := "res" }
      (.cast (.binary .add (.var "res") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩)))),
   .assign .localVar { base := "bits" }
      (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "bits") (.intLit 1))]

theorem bitmapMsbLoopSource {cfg : Config} {evm : EVM.State} (n : Nat)
    (hn : n < UInt256.size) (frame : Frame) (res : UInt256)
    (hr : frame.locals.get? "res" = some (.int res.toNat))
    (hb : frame.locals.get? "bits" = some (.int n)) :
    ∃ frame', ExecStmt cfg frame evm bitmapMsbLoop (.ok frame' evm) ∧
      frame'.locals.get? "res" = some (.int (res + UInt256.ofNat n.size).toNat) := by
  induction n using Nat.strong_induction_on generalizing frame res with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      refine ⟨frame, ExecStmt.whileFalse ?_, ?_⟩
      · simp only [evalExpr?, hb, bind, pure, EvalResult.bind, EvalResult.ofOption,
          evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq]
        rfl
      · simpa only [Nat.size_zero, wordAddNat_zero] using hr
    · let frame₁ := { frame with
        locals := frame.locals.insert "res" (.int (res + UInt256.ofNat 1).toNat) }
      let frame₂ := { frame₁ with locals := frame₁.locals.insert "bits" (.int (Int.ofNat (n / 2))) }
      have hb₁ : frame₁.locals.get? "bits" = some (.int n) := by
        simpa only [frame₁, store_get_ne _ _ (show ("res" == "bits") = false from rfl)] using hb
      have hstep : ExecBlock cfg frame evm
          [.assign .localVar { base := "res" }
            (.cast (.binary .add (.var "res") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩)))),
           .assign .localVar { base := "bits" }
            (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "bits") (.intLit 1))]
          (.ok frame₂ evm) := by
        refine ExecBlock.consNormal
          (execLocalAssign (value := .int (res + UInt256.ofNat 1).toNat) hr ?_) ?_
        · exact evalWrappingAdd256 (a := res) (b := UInt256.ofNat 1)
            (by simp only [evalExpr?, hr, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl)
        · refine ExecBlock.consNormal
            (execLocalAssign (value := .int (Int.ofNat (n / 2))) hb₁ ?_) ExecBlock.nil
          have he := evalWordShiftRight (word := UInt256.ofNat n) (shift := ⟨1⟩)
            (cfg := cfg) (frame := frame₁) (evm := evm) (lhs := .var "bits") (rhs := .intLit 1)
            (by simp only [evalExpr?, hb₁, EvalResult.ofOption, UInt256.toNat_ofNat_of_lt hn])
            (by simp only [evalExpr?, pure]; rfl) (by decide)
          rw [shiftRight_toNat (UInt256.ofNat n) ⟨1⟩ (by decide),
            UInt256.toNat_ofNat_of_lt hn] at he
          exact he
      obtain ⟨frame', hloop, hres⟩ := ih (n / 2) (by omega) (by omega) frame₂ (res + UInt256.ofNat 1)
        (by simp only [frame₂, frame₁, store_get_ne _ _ (show ("bits" == "res") = false from rfl),
          store_get_self]) (by exact store_get_self _ _ _)
      refine ⟨frame', ExecStmt.whileTrue ?_ hstep hloop, ?_⟩
      · simp only [evalExpr?, hb, bind, pure, EvalResult.bind, EvalResult.ofOption,
          evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
          Int.natCast_eq_zero, hz, decide_false, Bool.not_false]
      · simpa only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
          wordAddNat_add, natSize_div_two hz, Nat.add_comm 1] using hres

theorem bitmapMsbSource {cfg : Config} {frame : Frame} {evm : EVM.State} {bitmap : UInt256}
    (hb : frame.locals.get? "bitmap" = some (.int bitmap.toNat)) :
    ∃ frame', ExecFuncBody cfg frame evm bitmapMsbFunction.body
      (.returned frame' evm (some [.int (bitmapMsb bitmap).toNat])) := by
  let maximum := UInt256.ofNat (2^256 - 1)
  let frame₁ := { frame with locals := frame.locals.insert "res" (.int maximum.toNat) }
  let frame₂ := { frame₁ with locals := frame₁.locals.insert "bits" (.int bitmap.toNat) }
  obtain ⟨frame', hloop, hr⟩ := bitmapMsbLoopSource (cfg := cfg) (evm := evm)
    bitmap.toNat bitmap.val.isLt frame₂ maximum
    (by simp only [frame₂, frame₁, store_get_ne _ _ (show ("bits" == "res") = false from rfl),
      store_get_self]) (store_get_self _ _ _)
  have he : maximum + UInt256.ofNat bitmap.toNat.size = bitmapMsb bitmap := by
    by_cases hz : bitmap.toNat = 0
    · simp only [hz, Nat.size_zero, wordAddNat_zero, bitmapMsb, UInt256.clz, if_true]
      rfl
    · apply u256_inj
      rw [bitmapMsb_toNat hz, natSize_eq_log2_succ hz, uadd_toNat]
      have hl : bitmap.toNat.log2 < 256 := (Nat.log2_lt hz).mpr bitmap.val.isLt
      rw [UInt256.toNat_ofNat_of_lt (n := bitmap.toNat.log2 + 1) (by change _ < 2^256; omega)]
      change (2^256 - 1 + (bitmap.toNat.log2 + 1)) % 2^256 = bitmap.toNat.log2
      rw [show 2^256 - 1 + (bitmap.toNat.log2 + 1) = 2^256 + bitmap.toNat.log2 by omega,
        Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [he] at hr
  refine ⟨frame', ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int maximum.toNat) (by
    norm_num [evalExpr?, maximum, UInt256.toNat, UInt256.ofNat]
    rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int bitmap.toNat) ?_) ?_
  · simp only [evalExpr?,
      store_get_ne _ _ (show ("res" == "bitmap") = false from rfl), hb, EvalResult.ofOption]
  · exact ExecBlock.consNormal hloop
      (ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, hr,
        EvalResult.ofOption, EvalResult.bind, bind, pure])))

theorem bitmapClearSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {bitmap bit : UInt256}
    (hb : frame.locals.get? "bitmap" = some (.int bitmap.toNat))
    (hi : frame.locals.get? "bit" = some (.int bit.toNat)) (hbit : bit.toNat < 256) :
    ExecFuncBody cfg frame evm bitmapClearFunction.body
      (.returned frame evm (some [.int (bitmapClear bitmap bit).toNat])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he := evalCast128 (evalWordBitAnd (cfg := cfg) (frame := frame) (evm := evm)
    (lhs := .var "bitmap") (a := bitmap)
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
    (evalWordBitNot (evalOneShiftLeft (expr := .var "bit") (bit := bit)
      (by simp only [evalExpr?, hi, EvalResult.ofOption]) hbit)))
  simp only [packedUInt128Int] at he
  simp only [evalExprs?, he, bind, pure, EvalResult.bind, bitmapClear]

end Benchmarks.Midnight
