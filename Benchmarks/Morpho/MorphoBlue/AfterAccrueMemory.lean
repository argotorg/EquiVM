import Benchmarks.Morpho.MorphoBlue.AccrueFunctionRefine
import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev afterAccrueMemoryFunction : FunctionDecl := contract.functions[21]!

def afterAccrueMemoryCost (accrued : Bool) (fee : UInt256) : Nat :=
  if accrued then 160 + if fee = ⟨0⟩ then 0 else 64 else 0

def afterAccrueMemoryFrame (base : Nat) (accrued : Bool) (fee : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "__fee" (.int (Int.ofNat fee.toNat))).insert "__accrued" (.bool accrued)).insert
      "__memory" (.int (Int.ofNat base)) }

theorem morphoAfterAccrueMemoryBody (base : Nat) (accrued : Bool) (fee : UInt256)
    (frame : Frame) (evm : EVM.State)
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat base)))
    (ha : frame.locals.get? "__accrued" = some (.bool accrued))
    (hf : frame.locals.get? "__fee" = some (.int (Int.ofNat fee.toNat))) :
    ∃ frame', ExecFuncBody config frame evm afterAccrueMemoryFunction.body
      (.returned frame' evm (some [.int (Int.ofNat (base + afterAccrueMemoryCost accrued fee))])) := by
  have hea : evalExpr? config frame evm (.var "__accrued") = .ok (.bool accrued) := by
    simp only [evalExpr?, ha, EvalResult.ofOption]
  cases accrued
  · refine ⟨frame, ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.iteFalse hea ExecBlock.nil) ?_)⟩
    apply ABlock.start.returns
    simp only [evalExpr?, hm, EvalResult.ofOption, afterAccrueMemoryCost, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  · let frame1 := { frame with locals := frame.locals.insert "__memory" (.int (Int.ofNat (base + 160))) }
    have hmem1 : frame1.locals.get? "__memory" = some (.int (Int.ofNat (base + 160))) := store_get_self _ _ _
    have hs1 : ExecStmt config frame evm
        (.assign .localVar ⟨"__memory", []⟩ (.binary .add (.var "__memory") (.intLit 160))) (.ok frame1 evm) :=
      ExecStmt.assign (safeTransferMemoryAdd_eval hm 160) (assignLocalWord hm)
    have hfee1 : evalExpr? config frame1 evm (.var "__fee") = .ok (.int (Int.ofNat fee.toNat)) := by
      simp only [evalExpr?, frame1, store_get_ne _ _ (show ("__memory" == "__fee") = false by decide), hf, EvalResult.ofOption]
    have hefee := evalWordNeZero hfee1
    by_cases hz : fee = ⟨0⟩
    · have hfalse : evalExpr? config frame1 evm (.binary .ne (.var "__fee") (.intLit 0)) = .ok (.bool false) := by
        simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hefee
      refine ⟨frame1, ExecFuncBody.execBlockRet (ExecBlock.consNormal
        (ExecStmt.iteTrue hea (ExecBlock.consNormal hs1 (ExecBlock.consNormal (ExecStmt.iteFalse hfalse ExecBlock.nil) ExecBlock.nil))) ?_)⟩
      apply ABlock.start.returns
      simp only [evalExpr?, hmem1, EvalResult.ofOption, afterAccrueMemoryCost, ↓reduceIte, hz, Nat.add_zero]
    · let frame2 := { frame1 with locals := frame1.locals.insert "__memory" (.int (Int.ofNat (base + 160 + 64))) }
      have hmem2 : frame2.locals.get? "__memory" = some (.int (Int.ofNat (base + 160 + 64))) := store_get_self _ _ _
      have hs2 : ExecStmt config frame1 evm
          (.assign .localVar ⟨"__memory", []⟩ (.binary .add (.var "__memory") (.intLit 64))) (.ok frame2 evm) :=
        ExecStmt.assign (safeTransferMemoryAdd_eval hmem1 64) (assignLocalWord hmem1)
      have htrue : evalExpr? config frame1 evm (.binary .ne (.var "__fee") (.intLit 0)) = .ok (.bool true) := by
        simpa only [decide_eq_true hz] using hefee
      refine ⟨frame2, ExecFuncBody.execBlockRet (ExecBlock.consNormal
        (ExecStmt.iteTrue hea (ExecBlock.consNormal hs1
          (ExecBlock.consNormal (ExecStmt.iteTrue htrue (ExecBlock.consNormal hs2 ExecBlock.nil)) ExecBlock.nil))) ?_)⟩
      apply ABlock.start.returns
      simp only [evalExpr?, hmem2, EvalResult.ofOption, afterAccrueMemoryCost, ↓reduceIte, if_neg hz, Nat.add_assoc]

theorem morphoAfterAccrueMemoryCall (base : Nat) (accrued : Bool) (fee : UInt256)
    (evm : EVM.State) (locals imms : Store) (args : List Expr) (retVar : Ident)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [.int (Int.ofNat base), .bool accrued, .int (Int.ofNat fee.toNat)]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Solc_afterAccrueMemory" args retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (base + afterAccrueMemoryCost accrued fee))), immutables := imms } evm) := by
  obtain ⟨frame', hb⟩ := morphoAfterAccrueMemoryBody base accrued fee (afterAccrueMemoryFrame base accrued fee imms) evm
    (by simp [afterAccrueMemoryFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [afterAccrueMemoryFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [afterAccrueMemoryFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  exact internalCallFunctionReturn (callee := afterAccrueMemoryFunction)
    (value := some [.int (Int.ofNat (base + afterAccrueMemoryCost accrued fee))]) he rfl rfl hb

end Benchmarks.Morpho.MorphoBlue
