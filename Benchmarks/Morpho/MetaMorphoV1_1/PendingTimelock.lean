import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.PackedStorage
import Benchmarks.Morpho.MetaMorphoV1_1.TupleReturns
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_030
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `pendingTimelock()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5595; reach lemma `metaMorphoV1_1ReachPendingTimelockBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem pendingTimelockBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "pendingTimelock" = none) :
    ExecTransitionBody config contract evm locals pendingTimelockTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.int (Int.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩)
          (UInt256.ofNat (2 ^ 192 - 1))).toNat),
          .int (Int.ofNat (UInt256.shiftRight
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩)
            ⟨192⟩).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hbase' : (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
      "pendingTimelock" = none := by
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hfirst := evalStorage_pendingTimelockValue evm _ (immStore v) hbase'
  have hsecond := evalStorage_pendingTimelockValidAt evm _ (immStore v) hbase'
  simp only [evalExprs?, hfirst, hsecond, bind, EvalResult.bind, pure]

set_option maxRecDepth 2000 in
theorem pendingTimelockReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5595⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      ((UInt256.land (codeOwnerStorageWord I σ ⟨17⟩)
          (UInt256.ofNat (2 ^ 192 - 1))).toByteArray ++
        (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨17⟩) ⟨192⟩).toByteArray) := by
  have rd5601 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5595_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd5612 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5601_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd5601
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5612
    (immWords := wordsOf (immStore v)) hstack rd5612
  exact returnPairMemory _ _ ▸ hret

set_option maxRecDepth 2000 in
theorem pendingTimelockRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5595⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5595_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem pendingTimelockRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5595⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd5601 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5595_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5601_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5601
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `pendingTimelock()`: the theorem `Correct.lean` routes selector 37 to. -/
theorem metaMorphoV1_1PendingTimelockBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 37)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 37) rfl hsel
  have hd : dispatchMsg contract I.calldata = some pendingTimelockTransition := by
    apply metaMorphoV1_1Dispatch_pendingTimelock <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (pendingTimelockTransition.params.map Param.name)
      (transitionSignature pendingTimelockTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachPendingTimelockBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact (pendingTimelockReturn v (by simp) hwv hsz hhi hsize rd).reEquivExecution
        hcode hd hdec (pendingTimelockBodyReturns v _ ∅ hwv hhi (by simp))
        (returnEquiv.returned rfl (uintPairReturnEncoding ⟨192, by decide⟩ ⟨64, by decide⟩
          (UInt256.land (codeOwnerStorageWord I σ ⟨17⟩)
          (UInt256.ofNat (2 ^ 192 - 1)))
          (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨17⟩) ⟨192⟩)
          (maskedWord_lt _ 192 (by decide)) (wordShiftRight_lt _ 192 (by decide))))
    · exact (pendingTimelockRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (pendingTimelockRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
