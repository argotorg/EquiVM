import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029

/-!
# MetaMorphoV1_1 `nonces(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5539; reach lemma `metaMorphoV1_1ReachNoncesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem noncesHelperReturns (evm : EVM.State) (imms : Store) (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecFuncBody config
      { contract := contract
        locals := (∅ : Store).insert "owner" (.address (AccountAddress.ofNat w.toNat))
        immutables := imms } evm
      [.return [.storage ⟨"_nonces", [.mindex (.var "owner")]⟩]]
      (.returned
        { contract := contract
          locals := (∅ : Store).insert "owner" (.address (AccountAddress.ofNat w.toNat))
          immutables := imms } evm
        (some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨7⟩ w)).toNat)])) := by
  exact ExecFuncBody.execBlockRet (ABlock.start.returns
    (evalStorage_nonces evm _ imms w (by simp) (store_get_self _ _ _) hcanon))

theorem noncesBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hget : locals.get? "owner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm locals noncesTransition.body
      (.returned
        { contract := contract
          locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "__c0"
            (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (solcMappingSlot ⟨7⟩ w)).toNat))
          immutables := immStore v }
        evm (some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨7⟩ w)).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal (ExecStmt.internalCallReturn
    (argVals := [.address (AccountAddress.ofNat w.toNat)])
    (calleeSolm :=
      { contract := contract
        locals := (∅ : Store).insert "owner" (.address (AccountAddress.ofNat w.toNat))
        immutables := immStore v })
    (value := some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (solcMappingSlot ⟨7⟩ w)).toNat)])
    ?_ (by rfl) (by rfl) (noncesHelperReturns evm (immStore v) w hcanon)) ?_
  · simp only [evalExprs?, evalExpr?,
      store_get_ne _ _ (by decide : ("__calldata" == "owner") = false),
      hget, EvalResult.ofOption, EvalResult.bind, bind, pure]
  · exact ABlock.start.returns (by
      simp only [resumeAfterInternalCall, collapseReturns, evalExpr?, store_get_self,
        EvalResult.ofOption])

set_option maxRecDepth 2000 in
theorem noncesReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5539⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨5572⟩ :: solcAddrMask :: R) mem aw rdata σ k' C' := by
  have rd5545 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5539_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd5557 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5545_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd5545
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5557
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5557
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem noncesReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨5539⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (codeOwnerStorageWord I σ (solcMappingSlot ⟨7⟩ (calldataWord I.calldata 4))).toByteArray := by
  obtain ⟨_, _, rd11163⟩ := noncesReachDecoder v (by omega) hwv hsz hhi hsize rd
  obtain ⟨_, _, rd5572⟩ := decodeAddressAt4 v (by simpa only [List.length_cons] using hstack)
    hcanon (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11163
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5572
    (immWords := wordsOf (immStore v)) (by omega) rd5572
  have hk := mappingScratchHash (UInt256.land (calldataWord I.calldata 4) solcAddrMask) ⟨7⟩
  exact solcAddrMask_clean hcanon ▸ hk ▸ (mappingScratchReturnMemory _ _ _ ▸ hret)

set_option maxRecDepth 2000 in
theorem noncesRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5539⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5539_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem noncesRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5539⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd5545 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5539_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5545_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5545
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem noncesRevertNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨5539⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd11163⟩ := noncesReachDecoder v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v (by simpa only [List.length_cons] using hstack) hnc rd11163

set_option maxRecDepth 2000 in
/-- `nonces(address)`: the theorem `Correct.lean` routes selector 38 to. -/
theorem metaMorphoV1_1NoncesBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 38)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 38) rfl hsel
  have hd : dispatchMsg contract I.calldata = some noncesTransition := by
    apply metaMorphoV1_1Dispatch_nonces <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachNoncesBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · exact (noncesReturn v (by simp) hwv hlen hhi hsize hcanon rd).reEquivExecution
            hcode hd (decodeCalldata_address_ok hlen hhi hcanon)
            (noncesBodyReturns v _ _ _ hwv hhi
              (store_get_self _ _ _) hcanon)
            (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have hrev := noncesRevertNoncanonical v (by simp) hwv hlen hhi hsize hcanon rd
          exact hrev.reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := noncesRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := noncesRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (noncesRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
