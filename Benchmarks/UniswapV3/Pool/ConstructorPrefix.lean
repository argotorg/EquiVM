import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.FactoryOwner
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def constructorParameterCalldata : ByteArray := ⟨#[0x89, 0x03, 0x57, 0x30]⟩

def constructorInitialFrame : Frame :=
  {contract := contract, locals := ∅, immutables := initialImmutables contract}

def constructorOriginalImms (original : AccountAddress) : Store :=
  (initialImmutables contract).insert "original" (.address original)

def constructorOriginalFrame (original : AccountAddress) : Frame :=
  {constructorInitialFrame with immutables := constructorOriginalImms original}

def constructorReadyFrame (original : AccountAddress) : Frame :=
  {constructorOriginalFrame original with locals := (∅ : Store).insert "_tickSpacing" (.int 0)}

def constructorCallFrame (original : AccountAddress) (ok : Bool) (out : ByteArray) : Frame :=
  {constructorReadyFrame original with
    locals := ((constructorReadyFrame original).locals.insert "parameterSuccess" (.bool ok)).insert
      "parameterData" (.bytes out)}

theorem constructorOriginalSource (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config constructorInitialFrame evm (contract.ctor.body.take 3)
      (.ok (constructorReadyFrame evm.executionEnv.codeOwner) evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address evm.executionEnv.codeOwner)
    (ty := .address) ?_ rfl rfl) ?_
  · simp only [evalExpr?, envValue, pure]
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem evalConstructorCodeGuard (evm : EVM.State) :
    evalExpr? config (constructorReadyFrame evm.executionEnv.codeOwner) evm
      (.binary .gt (.extCodeSize (.env .caller)) (.intLit 0)) =
      .ok (.bool (decide (0 <
        (extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val)).toNat))) :=
  evalExpr_codeGuard_of_accounts_eq rfl (accountAddress_roundtrip evm.executionEnv.source).symm
    (by simp only [evalExpr?, envValue, pure])

theorem constructorPrefixSource (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩) :
    ExecBlock config constructorInitialFrame evm (contract.ctor.body.take 4)
      (.ok (constructorReadyFrame evm.executionEnv.codeOwner) evm) := by
  have hpos : 0 < (extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val)).toNat := by
    by_contra h
    exact hcode (uint256_toNat_eq_zero (by omega))
  change ExecBlock _ _ _ (contract.ctor.body.take 3 ++ [(contract.ctor.body[3]!)]) _
  exact execBlock_append_ok (constructorOriginalSource evm hwv)
    (ExecBlock.consNormal (ExecStmt.requireTrue
      (by simpa only [hpos, decide_true] using evalConstructorCodeGuard evm)) ExecBlock.nil)

theorem constructorCallSource (evm evm' : EVM.State) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (ok, evm', out) false) :
    ExecStmt config (constructorReadyFrame evm.executionEnv.codeOwner) evm (contract.ctor.body[4]!)
      (.ok (constructorCallFrame evm.executionEnv.codeOwner ok out) evm') :=
  lowLevelCallWithPermSource (by simp only [evalExpr?, envValue, pure])
    (by simp only [evalExpr?, pure])
    (by simp only [evalExpr?, pure, constructorParameterCalldata]) hcall

theorem evalConstructorSuccess (original : AccountAddress) (evm : EVM.State)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (constructorCallFrame original ok out) evm (.var "parameterSuccess") =
      .ok (.bool ok) := by
  apply evalExpr_var_get
  simp only [constructorCallFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem evalConstructorData (original : AccountAddress) (evm : EVM.State)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (constructorCallFrame original ok out) evm (.var "parameterData") =
      .ok (.bytes out) := evalExpr_var_get Std.HashMap.getElem?_insert_self

theorem constructorRevertsNonpayable (evm : EVM.State) (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem constructorRevertsNoCode (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) = ⟨0⟩) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 contract.ctor.body]
  apply execBlock_append_ok (constructorOriginalSource evm hwv)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hcode] using evalConstructorCodeGuard evm))

theorem constructorRevertsCall (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (false, evm', out) false) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 contract.ctor.body]
  apply execBlock_append_ok (constructorPrefixSource evm hwv hcode)
  exact ExecBlock.consNormal (constructorCallSource evm evm' false out hcall)
    (ExecBlock.consRevert (ExecStmt.requireFalse (evalConstructorSuccess _ evm' false out)))

theorem constructorAfterCallSource (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (true, evm', out) false) :
    ExecBlock config constructorInitialFrame evm (contract.ctor.body.take 6)
      (.ok (constructorCallFrame evm.executionEnv.codeOwner true out) evm') := by
  change ExecBlock _ _ _ (contract.ctor.body.take 4 ++ (contract.ctor.body.drop 4).take 2) _
  exact execBlock_append_ok (constructorPrefixSource evm hwv hcode)
    (ExecBlock.consNormal (constructorCallSource evm evm' true out hcall)
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalConstructorSuccess _ evm' true out)) ExecBlock.nil))

end Benchmarks.UniswapV3.Pool
