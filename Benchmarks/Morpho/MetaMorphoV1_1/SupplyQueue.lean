import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_008

/-!
# MetaMorphoV1_1 `supplyQueue(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 861; reach lemma `metaMorphoV1_1ReachSupplyQueueBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem supplyQueueBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (i : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "supplyQueue" = none)
    (hget : locals.get? "arg0" = some (.int (Int.ofNat i.toNat)))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat) :
    ExecTransitionBody config contract evm locals supplyQueueTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) + i)))])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ABlock.start.returns
  exact evalStorage_supplyQueue evm _ (immStore v) i
    (by rw [store_get_ne _ _ (by decide)]; exact hbase)
    (by rw [store_get_ne _ _ (by decide)]; exact hget) hbound

theorem supplyQueueBodyRevertsBounds (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (i : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "supplyQueue" = none)
    (hget : locals.get? "arg0" = some (.int (Int.ofNat i.toNat)))
    (hbound : ¬ i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat) :
    ExecTransitionBody config contract evm locals supplyQueueTransition.body
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  have hread := evalStorage_arrayIndex_revert (cfg := config)
    (solm :=
      { contract := contract,
        locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata),
        immutables := immStore v }) (evm := evm) "supplyQueue" "arg0" i.toNat
    (by rw [store_get_ne _ _ (by decide)]; exact hbase)
    (by rw [store_get_ne _ _ (by decide)]; exact hget)
    (by rw [supplyQueueBounds, if_neg hbound])
  simp only [evalExprs?, hread, bind, EvalResult.bind]

set_option maxRecDepth 2000 in
theorem supplyQueueReachBounds {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨861⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨879⟩ R mem aw rdata σ k' C' := by
  have rd867 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_861_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd879 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_867_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd867
  exact ⟨_, _, rd879⟩

set_option maxRecDepth 2000 in
theorem supplyQueueReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hbound : (calldataWord I.calldata 4).toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨861⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (codeOwnerStorageWord I σ
        (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) +
          calldataWord I.calldata 4)).toByteArray := by
  obtain ⟨_, _, rd879⟩ := supplyQueueReachBounds v (by omega) hwv hsz hhi hsize rd
  obtain ⟨_, _, rd892⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_879_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by
      change UInt256.isZero (UInt256.lt (calldataWord I.calldata 4)
        (codeOwnerStorageWord I σ ⟨20⟩)) = ⟨0⟩
      rw [ult_one hbound]
      decide) rd879
  have rd11535 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_892
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd892
  obtain ⟨_, _, rd902⟩ := supplyQueueIndex v (by simpa using hstack) hbound
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11535
  exact arrayGetterReturn v (by omega)
    (wordAt0Mem_size_96 ⟨20⟩ solcFreePtrMem_size)
    (wordAt0Mem_read64 ⟨20⟩ solcFreePtrMem_size solcFreePtrMem_read64) rd902

set_option maxRecDepth 2000 in
theorem supplyQueueRevertBounds {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hbound : ¬ (calldataWord I.calldata 4).toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨861⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd879⟩ := supplyQueueReachBounds v hstack hwv hsz hhi hsize rd
  obtain ⟨_, _, rd917⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_879_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.isZero (UInt256.lt (calldataWord I.calldata 4)
        (codeOwnerStorageWord I σ ⟨20⟩)) ≠ ⟨0⟩
      rw [ult_zero (Nat.le_of_not_gt hbound)]
      decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd879
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v))
    (by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_879_taken_stack] using hstack) rd917

set_option maxRecDepth 2000 in
theorem supplyQueueRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨861⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_861_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem supplyQueueRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨861⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd867 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_861_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_867_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd867
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in

/-- `supplyQueue(uint256)`: the theorem `Correct.lean` routes selector 75 to. -/
theorem metaMorphoV1_1SupplyQueueBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 75)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 75) rfl hsel
  have hd : dispatchMsg contract I.calldata = some supplyQueueTransition := by
    apply metaMorphoV1_1Dispatch_supplyQueue <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSupplyQueueBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec := decodeCalldata_uint256_ok (x := "arg0") hlen hhi
        by_cases hbound : (calldataWord I.calldata 4).toNat <
            (codeOwnerStorageWord I σ ⟨20⟩).toNat
        · exact (supplyQueueReturn v (by simp) hwv hlen hhi hsize hbound rd).reEquivExecution
            hcode hd hdec (supplyQueueBodyReturns v _ _ _ hwv hhi
              (by simp) (store_get_self _ _ _) hbound)
            (returnEquiv.returned rfl (bytes32ReturnEncoding _))
        · exact (supplyQueueRevertBounds v (by simp) hwv hlen hhi hsize
            hbound rd).reEquivExecutionRevert
            hcode hd hdec
              (supplyQueueBodyRevertsBounds v _ _ _ hwv hhi
                (by simp) (store_get_self _ _ _) hbound)
      · have hrev := supplyQueueRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := supplyQueueRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_uint256_none_short (by omega))
  · exact dispatchedRevert hcode hd (supplyQueueRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
