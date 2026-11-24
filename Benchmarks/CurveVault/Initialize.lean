import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.InitializeABI
import Benchmarks.CurveVault.InitializeCore
import Benchmarks.CurveVault.InitializeMemory
import Benchmarks.CurveVault.InitializeGuard

variable {fork : Ethereum.Fork}

/-!
# Vault `initialize(address,address,address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body (its own `calldatasize`/`callvalue` guard first), the Stele body evaluation, and the
`…Body` theorem `Correct.lean` consumes.
Dispatcher: bucket 0, arm entry pc 73; reach lemma `vaultReachInitializeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

set_option maxRecDepth 2000000

/-- `initialize(address,address,address,address)`: the theorem `Correct.lean` routes selector 45 to. -/
theorem vaultInitializeBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 45)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 45) rfl hsel
  have hd : dispatchMsg contract I.calldata = some initializeTransition := by
    apply vaultDispatch_initialize
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := initializeTransition) (pc := UInt256.ofNat 158)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 132 < UInt256.size) (by decide +kernel) (by native_decide)
    (vaultInitializeDecodeShort I.calldata hsz) (vaultReachInitializeBody hcode hsz hsize hsel)
  intro hvalue hargs k C rd158
  by_cases ha : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · have rdFail := vaultBlocks.vault_block_158_taken (by simp)
      (fun hz => ha (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rd158
    exact (vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_158_taken_stack]) rdFail).reEquivDecodingFailed
      hcode hd (by rw [vaultInitializeDecode _ hargs, if_neg ha]) rfl rfl
  have rd170 := vaultBlocks.vault_block_158_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ ha) rd158
  by_cases hc : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · have rdFail := vaultBlocks.vault_block_170_taken (by simp)
      (fun hz => hc (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rd170
    exact (vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_170_taken_stack]) rdFail).reEquivDecodingFailed
      hcode hd (by rw [vaultInitializeDecode _ hargs, if_pos ha, if_neg hc]) rfl rfl
  have rd184 := vaultBlocks.vault_block_170_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hc) rd170
  by_cases ht : (calldataWord I.calldata 68).toNat < EVM.addressModulus
  swap
  · have rdFail := vaultBlocks.vault_block_184_taken (by simp)
      (fun hz => ht (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rd184
    exact (vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_184_taken_stack]) rdFail).reEquivDecodingFailed
      hcode hd (by rw [vaultInitializeDecode _ hargs, if_pos ha, if_pos hc, if_neg ht]) rfl rfl
  have rd198 := vaultBlocks.vault_block_184_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ ht) rd184
  by_cases hl : (calldataWord I.calldata 100).toNat < EVM.addressModulus
  swap
  · have rdFail := vaultBlocks.vault_block_198_taken (by simp)
      (fun hz => hl (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rd198
    exact (vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_198_taken_stack]) rdFail).reEquivDecodingFailed
      hcode hd (by rw [vaultInitializeDecode _ hargs, if_pos ha, if_pos hc, if_pos ht, if_neg hl]) rfl rfl
  have rd212 := vaultBlocks.vault_block_198_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hl) rd198
  let amm := calldataWord I.calldata 4
  let controller := calldataWord I.calldata 36
  let token := calldataWord I.calldata 68
  let collateral := calldataWord I.calldata 100
  let locals := vaultInitializeLocals amm controller token collateral
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes I.calldata = some locals := by
    rw [vaultInitializeDecode _ hargs, if_pos ha, if_pos hc, if_pos ht, if_pos hl]
  have hbase : locals.get? "_borrowed_token" = none := by
    simp only [locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    rfl
  have hload : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerStorageWord I σ ⟨0⟩ :=
    codeOwnerStorageWord_initState _
  have hguard := vaultInitializeGuardEval evm locals hbase
    (by rw [hload]; exact vaultSlotWord_canonical hwf 0 (by omega))
  rw [hload] at hguard
  by_cases hz : codeOwnerStorageWord I σ ⟨0⟩ = ⟨0⟩
  swap
  · obtain ⟨k', C', rdFail⟩ := vaultBlocks.vault_block_212_taken (by simp) hz (by native_decide) rd212
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_212_taken_stack]) rdFail
    have hsource : ExecTransitionBody fork config contract evm locals initializeTransition.body .reverted :=
      ExecFuncBody.execBlockRevert (nonpayableSecondRequireReverts hvalue
        (by simpa only [hz, decide_false] using hguard))
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  obtain ⟨k', C', rd221⟩ := vaultBlocks.vault_block_212_fallthrough (by simp) hz rd212
  have hguardTrue : evalExpr? config {contract := contract, locals := locals} evm vaultInitializeGuardExpr = .ok (.bool true) := by
    simpa only [hz, decide_true] using hguard
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have rd223 := rd221.push1 (UInt256.ofNat 128) (by native_decide)
      (by simp [vaultBlocks.vault_block_212_fallthrough_stack])
    have rd224 := RD.genMload rd223 (by native_decide)
      (by simp [vaultBlocks.vault_block_212_fallthrough_stack])
    have rd225 := rd224.push0 (by native_decide)
      (by simp [vaultBlocks.vault_block_212_fallthrough_stack])
    have hstatic := rd225.sstoreStatic hp (by native_decide)
      (by simp [vaultBlocks.vault_block_212_fallthrough_stack])
    have hsource : ExecTransitionBody fork config contract evm locals initializeTransition.body .staticViolation := by
      apply ExecFuncBody.execBlockStatic
      apply nonpayableRequireAssignStorageBlockStatic hvalue hguardTrue
        (show evalExpr? config {contract := contract, locals := locals} evm (.var "_borrowed_token_") =
          .ok (.address (AccountAddress.ofNat token.toNat)) by
          simp only [evalExpr?, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
        (vaultAssignScalarAddress evm locals "_borrowed_token" ⟨0⟩ (AccountAddress.ofNat token.toNat) hbase rfl rfl) hp
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  let mem := vaultInitializeMemory (vaultDispatchMemory ⟨4173887070⟩) amm controller token collateral
  have hmem0 : (vaultDispatchMemory ⟨4173887070⟩).size ≤ 64 := by native_decide
  obtain ⟨hmem, hma, hmc, hmt, hml⟩ := vaultInitializeMemory_facts
    (vaultDispatchMemory ⟨4173887070⟩) amm controller token collateral hmem0
  change RD fork vaultBytecode I (Sat256.ofUInt256 g) evm (UInt256.ofNat 221)
    [⟨70026204933037701⟩, solcSelectorWord I] mem _ ByteArray.empty σ k' C' at rd221
  rcases vaultInitializeAfterGuard SourceState.init ha hc ht hl hmem hma hmc hmt hml hperm
    (by repeat' apply memoryActive_le (bound := 10) ?_ (by decide +kernel); decide +kernel)
    (by simp) rd221 with ⟨evm', σ', locals', hbody, hs', hret⟩ | ⟨hbody, hrev⟩
  · have hsource : ExecTransitionBody fork config contract evm locals initializeTransition.body
        (.returned {contract := contract, locals := locals'} evm' none) :=
      ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
        (ExecBlock.consNormal (ExecStmt.requireTrue hguardTrue) hbody))
    exact hret.reEquivExecutionGen hcode hd hdec hsource hs'.accounts
      (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hsource : ExecTransitionBody fork config contract evm locals initializeTransition.body .reverted :=
      ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
        (ExecBlock.consNormal (ExecStmt.requireTrue hguardTrue) hbody))
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultInitializeBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 45)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultInitializeBodyCore hwf hcode hsize hsel

end Benchmarks.CurveVault
