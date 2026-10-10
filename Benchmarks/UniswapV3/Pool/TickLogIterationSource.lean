import Benchmarks.UniswapV3.Pool.TickLogIterationWords
import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickLogScaledExpr : Expr :=
  .binary (.shr (.uint ⟨256, by decide⟩))
    (.cast (.binary .mul (.var "r") (.var "r")) (.elem (.int (.uint ⟨256, by decide⟩))))
    (.intLit 127)

def tickLogAccExpr (name : String) (bits : Nat) : Expr :=
  .binary (.bitOr (.sint ⟨256, by decide⟩)) (.var "log_2")
    (.binary (.shl (.sint ⟨256, by decide⟩)) (.var name) (.intLit (Int.ofNat bits)))

def tickLogIterationHead (name : String) (bits : Nat) : List Stmt :=
  [.assign .localVar ⟨"r", []⟩ tickLogScaledExpr,
   .letDecl name none (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "r") (.intLit 128)),
   .assign .localVar ⟨"log_2", []⟩ (tickLogAccExpr name bits)]

def tickLogNextStmt (name : String) : Stmt :=
  .assign .localVar ⟨"r", []⟩
    (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "r") (.var name))

def tickLogIterationBody (name : String) (bits : Nat) : List Stmt :=
  tickLogIterationHead name bits ++ [tickLogNextStmt name]

theorem tickLogIterationHeadSource {frame : Frame} {evm : EVM.State}
    (r log : UInt256) (name : String) (bits : Nat)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat r.toNat)))
    (hl : frame.locals.get? "log_2" = some (.int (signedWordInt log)))
    (hnr : name ≠ "r") (hnl : name ≠ "log_2") (hbits : bits < 256) :
    ∃ frame', ExecBlock config frame evm (tickLogIterationHead name bits) (.ok frame' evm) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (tickLogScaled r).toNat)) ∧
      frame'.locals.get? "log_2" = some (.int (signedWordInt (tickLogAccumulate log r bits))) ∧
      frame'.locals.get? name = some (.int (Int.ofNat (tickLogDigit r).toNat)) ∧
      (∀ key, key ≠ "r" → key ≠ "log_2" → key ≠ name →
        frame'.locals.get? key = frame.locals.get? key) := by
  let f1 : Frame :=
    {frame with locals := frame.locals.insert "r" (.int (Int.ofNat (tickLogScaled r).toNat))}
  let f2 : Frame :=
    {f1 with locals := f1.locals.insert name (.int (Int.ofNat (tickLogDigit r).toNat))}
  let f3 : Frame :=
    {f2 with locals := f2.locals.insert "log_2" (.int (signedWordInt (tickLogAccumulate log r bits)))}
  have hr1 : f1.locals.get? "r" = some (.int (Int.ofNat (tickLogScaled r).toNat)) := by
    change f1.locals["r"]? = _
    exact Std.HashMap.getElem?_insert_self
  have hr2 : f2.locals.get? "r" = some (.int (Int.ofNat (tickLogScaled r).toNat)) := by
    simpa [f2, Std.HashMap.getElem?_insert, hnr] using hr1
  have hl2 : f2.locals.get? "log_2" = some (.int (signedWordInt log)) := by
    simpa [f2, f1, Std.HashMap.getElem?_insert, hnl] using hl
  have hn2 : f2.locals.get? name = some (.int (Int.ofNat (tickLogDigit r).toNat)) := by
    change f2.locals[name]? = _
    exact Std.HashMap.getElem?_insert_self
  refine ⟨f3, ?_, ?_, ?_, ?_, ?_⟩
  · refine ExecBlock.consNormal (solm' := f1) (evm' := evm)
      (ExecStmt.assign (value := .int (Int.ofNat (tickLogScaled r).toNat)) ?_
        (assignLocalVarBase_frame hr)) ?_
    · have he := evalExpr_var_get (cfg := config) (evm := evm) hr
      exact evalExpr_word_shr 127 (by decide) (evalExpr_word_mul he he)
    refine ExecBlock.consNormal (solm' := f2) (evm' := evm) (ExecStmt.letDecl ?_) ?_
    · exact evalExpr_word_shr 128 (by decide) (evalExpr_var_get hr1)
    refine ExecBlock.consNormal (solm' := f3) (evm' := evm)
      (ExecStmt.assign (value := .int (signedWordInt (tickLogAccumulate log r bits))) ?_
        (assignLocalVarBase_frame hl2)) ExecBlock.nil
    have hs := evalExpr_sint_shl bits hbits (evalExpr_var_get (cfg := config) (evm := evm) hn2)
    have ho := evalExpr_sint_lor (evalExpr_var_get (cfg := config) (evm := evm) hl2) hs
    simpa only [tickLogAccExpr, tickLogAccumulate, wordOfInt_signedWordInt,
      wordOfInt_ofNat_toNat] using ho
  · simpa [f3, Std.HashMap.getElem?_insert] using hr2
  · change f3.locals["log_2"]? = _
    exact Std.HashMap.getElem?_insert_self
  · simpa [f3, Std.HashMap.getElem?_insert, Ne.symm hnl] using hn2
  · intro key hkr hkl hkn
    simp [f3, f2, f1, Std.HashMap.getElem?_insert, Ne.symm hkr, Ne.symm hkl, Ne.symm hkn]

theorem tickLogIterationSource {frame : Frame} {evm : EVM.State}
    (r log : UInt256) (name : String) (bits : Nat)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat r.toNat)))
    (hl : frame.locals.get? "log_2" = some (.int (signedWordInt log)))
    (hnr : name ≠ "r") (hnl : name ≠ "log_2") (hbits : bits < 256) :
    ∃ frame', ExecBlock config frame evm (tickLogIterationBody name bits) (.ok frame' evm) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (tickLogNext r).toNat)) ∧
      frame'.locals.get? "log_2" = some (.int (signedWordInt (tickLogAccumulate log r bits))) ∧
      (∀ key, key ≠ "r" → key ≠ "log_2" → key ≠ name →
        frame'.locals.get? key = frame.locals.get? key) := by
  obtain ⟨mid, hs, hr', hl', hn', hkeep⟩ := tickLogIterationHeadSource r log name bits hr hl hnr hnl hbits
  let out : Frame :=
    {mid with locals := mid.locals.insert "r" (.int (Int.ofNat (tickLogNext r).toNat))}
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · apply execBlock_append_ok hs
    refine ExecBlock.consNormal
      (ExecStmt.assign (value := .int (Int.ofNat (tickLogNext r).toNat)) ?_
        (assignLocalVarBase_frame hr')) ExecBlock.nil
    exact evalExpr_word_shr_by (evalExpr_var_get hr') (evalExpr_var_get hn')
      (lt_trans (tickLogDigit_lt r) (by decide))
  · change out.locals["r"]? = _
    exact Std.HashMap.getElem?_insert_self
  · simpa [out, Std.HashMap.getElem?_insert] using hl'
  · intro key hkr hkl hkn
    change out.locals[key]? = frame.locals[key]?
    simpa [out, Std.HashMap.getElem?_insert, Ne.symm hkr] using hkeep key hkr hkl hkn

end Benchmarks.UniswapV3.Pool
