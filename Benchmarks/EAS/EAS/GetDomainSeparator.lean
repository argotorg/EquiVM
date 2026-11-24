import Benchmarks.EAS.EAS.DomainEVM
import Benchmarks.EAS.EAS.ReturnWord

variable {fork : Ethereum.Fork}

/-! # EAS `getDomainSeparator()` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private def getDomainRest : Body := [
  .internalCall "_domainSeparatorV4" [.var "$EAS.freeMemory"] "__c0$allocation",
  .letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1),
  .return [.var "__c0"]]

private theorem getDomain_body : getDomainSeparatorTransition.body = easEntryPrefix ++ getDomainRest := by
  native_decide

private def getDomainLocals (locals : Store) (cd : ByteArray) (v : EASImmutables) (owner : AccountAddress) : Store :=
  unpackHeapLocals
    ((easEntryLocals locals cd).insert "__c0$allocation" (.tuple [wordBytes32Value (domainWord v owner),
      .int (Int.ofNat (domainNext v owner 224))]))
    "__c0" "$EAS.freeMemory" (wordBytes32Value (domainWord v owner)) (domainNext v owner 224)

private theorem getDomainSource_ok {cfg : Config} {evm : EVM.State} {locals : Store} (v : EASImmutables)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecTransitionBody fork cfg contract evm locals getDomainSeparatorTransition.body
      (.returned {
        contract := contract
        locals := getDomainLocals locals evm.executionEnv.calldata v evm.executionEnv.codeOwner
        immutables := immStore v} evm (some [wordBytes32Value (domainWord v evm.executionEnv.codeOwner)])) (immStore v) := by
  rw [getDomain_body]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (easEntryPrefix_ok hv hsz hsize hs)
  have hh : (easEntryLocals locals evm.executionEnv.calldata).get? "$EAS.freeMemory" = some (.int (Int.ofNat (224 : Nat))) := by
    simp only [easEntryLocals, store_get_ne _ _ (by decide : ("__calldata" == "$EAS.freeMemory") = false), store_get_self]
    rfl
  have hcall := domainCall_ok (fork := fork) (cfg := cfg) (evm := evm) v
    (retVar := "__c0$allocation") (locals := easEntryLocals locals evm.executionEnv.calldata)
    (show evalExpr? cfg {
      contract := contract
      locals := easEntryLocals locals evm.executionEnv.calldata
      immutables := immStore v} evm (.var "$EAS.freeMemory") = .ok (.int (Int.ofNat (224 : Nat))) from
      by simp only [evalExpr?, hh, EvalResult.ofOption]) (Or.inr (by decide))
  apply ExecBlock.consNormal hcall
  have hunpack := unpackHeapResult (fork := fork) (cfg := cfg) (evm := evm)
    (frame := {
      contract := contract
      locals := (easEntryLocals locals evm.executionEnv.calldata).insert "__c0$allocation"
        (.tuple [wordBytes32Value (domainWord v evm.executionEnv.codeOwner),
          .int (Int.ofNat (domainNext v evm.executionEnv.codeOwner 224))])
      immutables := immStore v}) (result := "__c0") (cursor := "$EAS.freeMemory") (old := .int 224)
    (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("__c0$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)
  apply execBlock_append hunpack
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [unpackHeapLocals, evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "__c0") = false), store_get_self,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

private def getDomainInitialMemory : ByteArray := Reasoning.Theory.writeWord ByteArray.empty 64 ⟨224⟩

private theorem getDomainEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 9 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨762⟩ R getDomainInitialMemory aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ (domainWord v ee.codeOwner).toByteArray := by
  have rd1 := easBlocks.eas_block_762 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  change RD fork _ _ _ _ ⟨13959⟩ (⟨771⟩ :: ⟨32⟩ :: R) getDomainInitialMemory _ _ _ _ _ at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := easDomain_ok (heap := ⟨224⟩) v (by simp only [List.length_cons]; omega) (by native_decide) (by decide)
    (Or.inr (by decide)) (by rw [easPatchedValidJumps v]; jump_dest) rd1
  exact easReturnWord v (by omega) rd2

theorem easGetDomainSeparatorBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 18)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 18) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getDomainSeparatorTransition := by
    apply easDispatch_getDomainSeparator (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hdec : config.externalABI.decodeCalldata?
      (getDomainSeparatorTransition.params.map Param.name)
      (transitionSignature getDomainSeparatorTransition).paramTypes I.calldata = some (∅ : Store) :=
    by
      change decodeCalldataWithMode Syntax.abiDecodeMode [] [] I.calldata = some (∅ : Store)
      exact decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rd⟩ := easReachGetDomainSeparatorBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_714_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases hs : I.calldata.size - 4 < 2^255
    · have rd2 := easBlocks.eas_block_720_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_ok hsz hsize hs) rd1
      have hout := getDomainEVM v (by simp) rd2
      refine RDret.reEquivExecution
        (retVal := some [wordBytes32Value (domainWord v I.codeOwner)])
        (cs := {contract := contract, locals := getDomainLocals ∅ I.calldata v I.codeOwner, immutables := immStore v})
        hcode hout hd hdec (getDomainSource_ok v hv hsz hsize hs) ?_
      exact returnEquiv_of_encode (bytes32ReturnEncoding _)
    · have rd2 := easBlocks.eas_block_720_taken (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_revert hsz hsize hs)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getDomain_body]
      exact easEntryBody_size_revert hv hsz hsize hs
  · have rd1 := easBlocks.eas_block_714_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
    rw [getDomain_body]
    exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
