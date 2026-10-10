import Benchmarks.UniswapV3.Pool.ConstructorModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalConstructorParameter (imms : Store) (original : AccountAddress) (evm : EVM.State)
    (out : ByteArray) (index : Nat) (value : Value)
    (hget : (constructorParameterValues out)[index]? = some value) :
    evalExpr? config {constructorDecodedFrame original out with immutables := imms} evm
      (.tupleGet (.var "__c0") index) = .ok value := by
  have he : evalExpr? config {constructorDecodedFrame original out with immutables := imms} evm
      (.var "__c0") = .ok (.tuple (constructorParameterValues out)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExpr?, he, tupleGetValue?, hget, EvalResult.ofOption, bind, EvalResult.bind]

theorem constructorDecodeSource (original : AccountAddress) (evm : EVM.State)
    (out : ByteArray) (hlen : 160 ≤ out.size) :
    ExecStmt config (constructorCallFrame original true out) evm (contract.ctor.body[6]!)
      (.ok (constructorDecodedFrame original out) evm) := by
  apply ExecStmt.letDecl
  simp only [evalExpr?, evalConstructorData, bind, EvalResult.bind]
  have hd := constructorParameterDecode out hlen
  simp only [constructorParameterTypes] at hd
  rw [show config.abiDecodeMode = .legacySolc05 from rfl, hd]
  rfl

theorem constructorFieldsSource (original : AccountAddress) (evm : EVM.State) (out : ByteArray) :
    ExecBlock config (constructorDecodedFrame original out) evm ((contract.ctor.body.drop 7).take 4)
      (.ok (constructorFieldsFrame original out) evm) := by
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address)
    (evalConstructorParameter _ original evm out 0 _ rfl) rfl rfl) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address)
    (evalConstructorParameter _ original evm out 1 _ rfl) rfl rfl) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address)
    (evalConstructorParameter _ original evm out 2 _ rfl) rfl rfl) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256, by decide⟩))
    (evalConstructorParameter _ original evm out 3 _ rfl) rfl ?_) ExecBlock.nil
  have hf := constructorFee_bounds out
  simp only [elemValueFits, decide_eq_true_eq]
  change 0 ≤ constructorFee out ∧ constructorFee out < 2 ^ 256
  exact ⟨hf.1, by omega⟩

theorem constructorSpacingSource (original : AccountAddress) (evm : EVM.State) (out : ByteArray) :
    ExecBlock config (constructorFieldsFrame original out) evm ((contract.ctor.body.drop 11).take 2)
      (.ok (constructorSpacingFrame original out) evm) := by
  have hget : (constructorFieldsFrame original out).locals.get? "_tickSpacing" = some (.int 0) := by
    simp only [constructorFieldsFrame, constructorDecodedFrame, constructorCallFrame,
      constructorReadyFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign
    (evalConstructorParameter _ original evm out 4 _ rfl) (assignLocalVarBase_frame hget)) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (constructorUnsignedSpacing out))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl ?_) ExecBlock.nil
  · have he : evalExpr? config
        {constructorFieldsFrame original out with
          locals := (constructorFieldsFrame original out).locals.insert "_tickSpacing"
            (.int (constructorSpacing out))} evm (.var "_tickSpacing") =
        .ok (.int (constructorSpacing out)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
    change evalExpr? config
      {constructorFieldsFrame original out with
        locals := (constructorFieldsFrame original out).locals.insert "_tickSpacing"
          (.int (constructorSpacing out))} evm
      (.cast (.var "_tickSpacing") (.elem (.int (.uint ⟨24, by decide⟩)))) = _
    simp only [evalExpr?, he, castValue?, EvalResult.ofOption, bind, EvalResult.bind,
      constructorUnsignedSpacing]
  · have hs := constructorUnsignedSpacing_bounds out
    simp only [elemValueFits, decide_eq_true_eq]
    change 0 ≤ constructorUnsignedSpacing out ∧ constructorUnsignedSpacing out < 2 ^ 256
    exact ⟨hs.1, by omega⟩

theorem constructorBeforeSpacingSource (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (true, evm', out) false) (hlen : 160 ≤ out.size) :
    ExecBlock config constructorInitialFrame evm (contract.ctor.body.take 13)
      (.ok (constructorSpacingFrame evm.executionEnv.codeOwner out) evm') := by
  change ExecBlock _ _ _ (contract.ctor.body.take 6 ++ (contract.ctor.body.drop 6).take 7) _
  apply execBlock_append_ok (constructorAfterCallSource evm evm' out hwv hcode hcall)
  apply ExecBlock.consNormal (constructorDecodeSource _ evm' out hlen)
  change ExecBlock config (constructorDecodedFrame evm.executionEnv.codeOwner out) evm'
    ((contract.ctor.body.drop 7).take 4 ++ (contract.ctor.body.drop 11).take 2) _
  exact execBlock_append_ok (constructorFieldsSource _ evm' out) (constructorSpacingSource _ evm' out)

theorem constructorRevertsShort (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (true, evm', out) false) (hshort : out.size < 160) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 6 contract.ctor.body]
  apply execBlock_append_ok (constructorAfterCallSource evm evm' out hwv hcode hcall)
  refine ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  simp only [evalExpr?, evalConstructorData, bind, EvalResult.bind]
  have hd := constructorParameterDecodeShort out hshort
  simp only [constructorParameterTypes] at hd
  rw [show config.abiDecodeMode = .legacySolc05 from rfl, hd]

end Benchmarks.UniswapV3.Pool
