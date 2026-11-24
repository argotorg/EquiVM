import Benchmarks.CurveVault.CeilDiv
import Benchmarks.CurveVault.TotalAssetsInternal
import Benchmarks.CurveVault.Memory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault


abbrev vaultMaxWord : UInt256 := UInt256.ofNat (UInt256.size - 1)

abbrev vaultConversionPrefix : List Stmt := contract.functions[28]!.body.take 2

theorem vaultConversionPrefixProvided {evm : State} {locals : Store} {total : UInt256}
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)))
    (hne : total ≠ vaultMaxWord) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionPrefix
      (.ok {contract := contract, locals := locals.insert "total_assets" (.int (Int.ofNat total.toNat))} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_varUInt256 harg))
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  · apply evalExpr_eq_int_false (b := 2 ^ 256 - 1) (evalExpr_varUInt256 (value := total) (by simp)) (by simp [evalExpr?, pure])
    intro hnat
    apply hne
    apply u256_inj
    change total.toNat = (UInt256.ofNat (UInt256.size - 1)).toNat
    rw [ulit_toNat' _ (by decide +kernel)]
    change (total.toNat : Int) = Int.ofNat (UInt256.size - 1) at hnat
    exact Int.ofNat.inj hnat

theorem vaultConversionPrefixComputed {evm evm' : State} {locals : Store} {callee : Frame} {total : UInt256}
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat vaultMaxWord.toNat)))
    (hbody : ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body
      (.returned callee evm' (some [.int (Int.ofNat total.toNat)]))) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionPrefix
      (.ok {contract := contract, locals :=
        ((locals.insert "total_assets" (.int (Int.ofNat vaultMaxWord.toNat))).insert
          "__c0" (.int (Int.ofNat total.toNat))).insert "total_assets" (.int (Int.ofNat total.toNat))} evm') := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_varUInt256 harg))
  refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
  · exact evalExpr_eq_int_true (b := 2 ^ 256 - 1) (evalExpr_varUInt256 (value := vaultMaxWord) (by simp)) (by simp [evalExpr?, pure]) (by decide +kernel)
  · have hcall := internalCallFunctionReturn (cfg := config) (evm := evm)
      (caller := {contract := contract, locals := locals.insert "total_assets" (.int (Int.ofNat vaultMaxWord.toNat))})
      (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (argVals := []) (retVar := "__c0")
      (by simp [evalExprs?, pure]) rfl rfl hbody
    apply ExecBlock.consNormal hcall
    refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) (evalExpr_varUInt256 (value := total) (by
      simp [collapseReturns])) ?_)
      ExecBlock.nil
    · apply assignLocalVarBase_ok
      simp only [collapseReturns, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
      rfl

theorem vaultConversionPrefixReverted {evm : State} {locals : Store}
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat vaultMaxWord.toNat)))
    (hbody : ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body .reverted) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionPrefix .reverted := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_varUInt256 harg))
  apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
  · exact evalExpr_eq_int_true (b := 2 ^ 256 - 1) (evalExpr_varUInt256 (value := vaultMaxWord) (by simp)) (by simp [evalExpr?, pure]) (by decide +kernel)
  · exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultTotalAssetsFunction)
      (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hbody)
end Benchmarks.CurveVault
