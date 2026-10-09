import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.MappingStructs
import Benchmarks.Morpho.MetaMorphoV1_1.TupleReturns
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_014

/-!
# MetaMorphoV1_1 `config(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1980; reach lemma `metaMorphoV1_1ReachConfigBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem configBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (bs : List UInt8) (w : UInt256)
    (hlen : bs.length = 32) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "config" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    ExecTransitionBody config contract evm locals configTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.int (Int.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
          (UInt256.ofNat (2 ^ 184 - 1))).toNat),
          wordToElem .bool (UInt256.land (UInt256.shiftRight
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
            ⟨184⟩) ⟨255⟩),
          .int (Int.ofNat (UInt256.shiftRight
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
            ⟨192⟩).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hbase' : (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
      "config" = none := by
    rw [store_get_ne _ _ (by decide)]
    exact hbase
  have hget' : (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).get? "arg0" =
      some (.fixedBytes abiBytes32Width bs) := by
    rw [store_get_ne _ _ (by decide)]
    exact hget
  have hfirst := evalStorage_configCap evm _ (immStore v) bs w hlen hbase' hget' hkey
  have hflag := evalStorage_configEnabled evm _ (immStore v) bs w hlen hbase' hget' hkey
  have hsecond := evalStorage_configRemovableAt evm _ (immStore v) bs w hlen hbase' hget' hkey
  simp only [evalExprs?, hfirst, hflag, hsecond, bind, EvalResult.bind, pure]

set_option maxRecDepth 2000 in
theorem configReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1980⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      ((UInt256.land
        (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4)))
        (UInt256.ofNat (2 ^ 184 - 1))).toByteArray ++
        ((UInt256.isZero (UInt256.isZero (UInt256.land
          (UInt256.shiftRight
            (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4)))
            ⟨184⟩) ⟨255⟩))).toByteArray ++
          (UInt256.shiftRight
            (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4)))
            ⟨192⟩).toByteArray)) := by
  have rd1986 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1980_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd1998 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1986_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd1986
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1998
    (immWords := wordsOf (immStore v)) hstack rd1998
  have hptr := mappingScratch_mload64 (calldataWord I.calldata 4) ⟨13⟩
  have hk := mappingScratchHash (calldataWord I.calldata 4) ⟨13⟩
  exact hk ▸ (returnTripleMemory _ _ _ _ hptr ▸ hret)

set_option maxRecDepth 2000 in
theorem configRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1980⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1980_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem configRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1980⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1986 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1980_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1986_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1986
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `config(bytes32)`: the theorem `Correct.lean` routes selector 62 to. -/
theorem metaMorphoV1_1ConfigBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 62)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 62) rfl hsel
  have hd : dispatchMsg contract I.calldata = some configTransition := by
    apply metaMorphoV1_1Dispatch_config <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachConfigBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · exact (configReturn v (by simp) hwv hlen hhi hsize rd).reEquivExecution
          hcode hd (decodeCalldata_bytes32_ok hlen hhi)
          (configBodyReturns v _ _ _ _ (calldata_first_word_length hlen) hwv hhi
            (by simp) (store_get_self _ _ _) (calldataBytes32Key hlen))
          (returnEquiv.returned rfl (uintBoolUintReturnEncoding ⟨184, by decide⟩ ⟨64, by decide⟩
            (UInt256.land
              (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4)))
              (UInt256.ofNat (2 ^ 184 - 1)))
            (UInt256.shiftRight
              (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4))) ⟨184⟩)
            (UInt256.shiftRight
              (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ (calldataWord I.calldata 4))) ⟨192⟩)
            (maskedWord_lt _ 184 (by decide)) (wordShiftRight_lt _ 192 (by decide))))
      · have hrev := configRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_bytes32_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := configRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_bytes32_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (configRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
