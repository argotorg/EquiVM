import Benchmarks.EAS.EAS.Allocate
import Benchmarks.EAS.EAS.MemoryCopy

variable {fork : Ethereum.Fork}

/-! # EAS `VERSION()` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private def versionRest : Body := [
  .internalCall "_allocate" [.intLit 64, .var "$EAS.freeMemory"] "allocation$allocation",
  .letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1),
  .return [.bytesLit "0.26".toUTF8]]

private theorem version_body : vERSIONTransition.body = easEntryPrefix ++ versionRest := by
  native_decide

private def versionFinalLocals (locals : Store) (cd : ByteArray) : Store :=
  easEntryLocals locals cd
    |>.insert "allocation$allocation" (.tuple [.tuple [], .int 288])
    |>.insert "allocation" (.tuple [])
    |>.insert "$EAS.freeMemory" (.int 288)

private theorem versionSource_ok {cfg : Config} {evm : EVM.State} {locals imms : Store}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecTransitionBody fork cfg contract evm locals vERSIONTransition.body
      (.returned
        { contract := contract
          locals := versionFinalLocals locals evm.executionEnv.calldata
          immutables := imms} evm (some [.bytes "0.26".toUTF8])) imms := by
  rw [version_body]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (easEntryPrefix_ok hv hsz hsize hs)
  refine ExecBlock.consNormal (allocateCall_ok (heap := 224) (size := 64) ?_ ?_ (by decide)) ?_
  · simp only [evalExpr?, pure]; rfl
  · simp only [evalExpr?, easEntryLocals,
      store_get_ne _ _ (by decide : ("__calldata" == "$EAS.freeMemory") = false), store_get_self,
      EvalResult.ofOption]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .tuple []) ?_) ?_
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption, EvalResult.bind, bind]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int 288) ?_ (assignLocalBase_ok (old := .int 224) ?_)) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("allocation" == "allocation$allocation") = false),
      store_get_self, EvalResult.ofOption, EvalResult.bind, bind]
    rfl
  · simp only [easEntryLocals,
      store_get_ne _ _ (by decide : ("allocation" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("allocation$allocation" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "$EAS.freeMemory") = false), store_get_self]
  exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

private def versionInitialMemory : ByteArray := Reasoning.Theory.writeWord ByteArray.empty 64 ⟨224⟩
private def versionAllocatedMemory : ByteArray := Reasoning.Theory.writeWord versionInitialMemory 64 ⟨288⟩
private def versionStringMemory : ByteArray :=
  easBlocks.eas_block_338_memory (mem := versionAllocatedMemory) (x0 := ⟨64⟩) (x1 := ⟨224⟩)
private def versionOutput : ByteArray :=
  (easEncodeBytesMemory ⟨224⟩ ⟨320⟩ versionStringMemory).readWithPadding 288 96

private theorem versionOutput_encoding : encodeReturnValue? .string (.bytes "0.26".toUTF8) = some versionOutput := by
  native_decide

private theorem versionEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (v : EASImmutables)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨321⟩ [] versionInitialMemory aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ versionOutput := by
  have rd1 := easBlocks.eas_block_321 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have hstack1 : easBlocks.eas_block_321_stack (mem := versionInitialMemory) (R := []) =
      [⟨224⟩, ⟨64⟩, ⟨338⟩, ⟨64⟩, ⟨224⟩, ⟨398⟩] := by native_decide
  rw [hstack1] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := easAllocate_ok v (by simp) (by decide)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  change RD fork _ _ _ _ ⟨338⟩ [⟨64⟩, ⟨224⟩, ⟨398⟩] versionAllocatedMemory _ _ _ _ _ at rd2
  obtain ⟨aw3, k3, C3, rd3⟩ := easBlocks.eas_block_338_packed (immWords := wordsOf (immStore v))
    (by simp) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hstack3 : easBlocks.eas_block_338_stack (mem := versionAllocatedMemory)
      (x0 := ⟨64⟩) (x1 := ⟨224⟩) (x2 := ⟨398⟩) (R := []) =
      [⟨224⟩, ⟨320⟩, ⟨398⟩, ⟨288⟩, ⟨288⟩] := by native_decide
  rw [hstack3] at rd3
  obtain ⟨aw4, k4, C4, rd4⟩ := easEncodeBytes v (by simp) (by native_decide)
    (by rw [easPatchedValidJumps v]; jump_dest) rd3
  have hnext : (UInt256.land (memLoad ⟨224⟩ versionStringMemory + ⟨31⟩)
      (UInt256.lnot ⟨31⟩) + ⟨320⟩) + ⟨32⟩ = ⟨384⟩ := by native_decide
  change RD fork _ _ _ _ ⟨398⟩ [(UInt256.land (memLoad ⟨224⟩ versionStringMemory + ⟨31⟩)
      (UInt256.lnot ⟨31⟩) + ⟨320⟩) + ⟨32⟩, ⟨288⟩, ⟨288⟩]
    (easEncodeBytesMemory ⟨224⟩ ⟨320⟩ versionStringMemory) _ _ _ _ _ at rd4
  rw [hnext] at rd4
  exact easBlocks.eas_block_398 (immWords := wordsOf (immStore v)) (by simp) rd4

theorem easVERSIONBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 21)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 21) rfl hsel
  have hd : dispatchMsg contract I.calldata = some vERSIONTransition := by
    apply easDispatch_vERSION (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hdec : config.externalABI.decodeCalldata?
      (vERSIONTransition.params.map Param.name)
      (transitionSignature vERSIONTransition).paramTypes I.calldata = some (∅ : Store) :=
    by
      change decodeCalldataWithMode Syntax.abiDecodeMode [] [] I.calldata = some (∅ : Store)
      exact decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rd⟩ := easReachVERSIONBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_273_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases hs : I.calldata.size - 4 < 2^255
    · have rd2 := easBlocks.eas_block_279_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_ok hsz hsize hs) rd1
      have hout := versionEVM v rd2
      refine RDret.reEquivExecution
        (retVal := some [.bytes "0.26".toUTF8])
        (cs := { contract := contract, locals := versionFinalLocals ∅ I.calldata, immutables := immStore v })
        hcode hout hd hdec (versionSource_ok hv hsz hsize hs) ?_
      exact returnEquiv_of_encode versionOutput_encoding
    · have rd2 := easBlocks.eas_block_279_taken (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_revert hsz hsize hs)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [version_body]
      exact easEntryBody_size_revert hv hsz hsize hs
  · have rd1 := easBlocks.eas_block_273_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
    rw [version_body]
    exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
