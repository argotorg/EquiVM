import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.PackedStorage
import Benchmarks.Morpho.MetaMorphoV1_1.TupleReturns
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_030
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `pendingGuardian()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5778; reach lemma `metaMorphoV1_1ReachPendingGuardianBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem pendingGuardianBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "pendingGuardian" = none) :
    ExecTransitionBody config contract evm locals pendingGuardianTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.address (AccountAddress.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩)
          solcAddrMask).toNat),
          .int (Int.ofNat (UInt256.land
          (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) ⟨160⟩)
          (UInt256.ofNat (2 ^ 64 - 1))).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hbase' : (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
      "pendingGuardian" = none := by
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hfirst := evalStorage_pendingGuardianValue evm _ (immStore v) hbase'
  have hsecond := evalStorage_pendingGuardianValidAt evm _ (immStore v) hbase'
  simp only [evalExprs?, hfirst, hsecond, bind, EvalResult.bind, pure]

set_option maxRecDepth 2000 in
theorem pendingGuardianReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5778⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      ((UInt256.land (codeOwnerStorageWord I σ ⟨15⟩)
          solcAddrMask).toByteArray ++
        (UInt256.land
          (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨15⟩) ⟨160⟩)
          (UInt256.ofNat (2 ^ 64 - 1))).toByteArray) := by
  have rd5784 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5778_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd5795 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5784_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd5784
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5795
    (immWords := wordsOf (immStore v)) hstack rd5795
  have hw := u256_land_comm (UInt256.ofNat (2 ^ 64 - 1))
    (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨15⟩) ⟨160⟩)
  exact hw ▸ (returnPairMemory _ _ ▸ hret)

set_option maxRecDepth 2000 in
theorem pendingGuardianRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5778⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5778_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem pendingGuardianRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5778⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd5784 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5778_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5784_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5784
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `pendingGuardian()`: the theorem `Correct.lean` routes selector 35 to. -/
theorem metaMorphoV1_1PendingGuardianBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 35)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 35) rfl hsel
  have hd : dispatchMsg contract I.calldata = some pendingGuardianTransition := by
    apply metaMorphoV1_1Dispatch_pendingGuardian <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (pendingGuardianTransition.params.map Param.name)
      (transitionSignature pendingGuardianTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachPendingGuardianBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact (pendingGuardianReturn v (by simp) hwv hsz hhi hsize rd).reEquivExecution
        hcode hd hdec (pendingGuardianBodyReturns v _ ∅ hwv hhi (by simp))
        (returnEquiv.returned rfl (addressUintPairReturnEncoding ⟨64, by decide⟩
          (codeOwnerStorageWord I σ ⟨15⟩) (UInt256.land
          (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨15⟩) ⟨160⟩)
          (UInt256.ofNat (2 ^ 64 - 1)))
          (maskedWord_lt _ 64 (by decide))))
    · exact (pendingGuardianRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (pendingGuardianRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
