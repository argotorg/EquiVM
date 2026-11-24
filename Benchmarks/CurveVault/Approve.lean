import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.ApproveInternal
import Benchmarks.CurveVault.ApproveArguments
import Benchmarks.CurveVault.AddressWord
import Benchmarks.CurveVault.MutatingLock
import Benchmarks.CurveVault.RuntimeBlocks_021

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultApprovePublicFunction : FunctionDecl := contract.functions[22]!

def vaultApprovePublicLocals (spender : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "_value" (.int (Int.ofNat value.toNat))).insert "_spender" (.address spender)

theorem vaultApprovePublicReturns {evm evm' : State} {spender : AccountAddress} {value : UInt256}
    (hbody : ExecFuncBody fork config
      {contract := contract, locals := vaultApproveLocals evm.executionEnv.source spender value}
      evm vaultApproveFunction.body
      (.returned {contract := contract, locals := vaultApproveLocals evm.executionEnv.source spender value}
        evm' none)) :
    ExecFuncBody fork config {contract := contract, locals := vaultApprovePublicLocals spender value}
      evm vaultApprovePublicFunction.body
      (.returned {contract := contract, locals := (vaultApprovePublicLocals spender value).insert "__c0" .unit}
        evm' (some [.bool true])) := by
  have hargs : evalExprs? config {contract := contract, locals := vaultApprovePublicLocals spender value} evm
      [.env .caller, .var "_spender", .var "_value"] =
      .ok [.address evm.executionEnv.source, .address spender, .int (Int.ofNat value.toNat)] := by
    simp only [evalExprs?, evalExpr?, envValue, vaultApprovePublicLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.bind, pure, bind]
    rfl
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := vaultApprovePublicLocals spender value})
    (callee := vaultApproveFunction) (name := "_approve") (retVar := "__c0") hargs rfl rfl hbody
  exact ExecFuncBody.execBlockRet <| ExecBlock.consNormal hcall <|
    ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, pure, bind]))

theorem vaultApproveBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 6) rfl hsel
  have hd : dispatchMsg contract I.calldata = some approveTransition := by
    apply vaultDispatch_approve
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := approveTransition) (pc := UInt256.ofNat 5947)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 68 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_addr_uint256_none_short hsz)
    (vaultReachApproveBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · have rdRevert := vaultBlocks.vault_block_5947_taken (by simp)
      (fun h => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5947_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_addr_uint256_none_noncanon hargs hcanon) rfl rfl
  let spender := calldataWord I.calldata 4
  let value := calldataWord I.calldata 36
  let locals := ((∅ : Store).insert "_spender" (.address (AccountAddress.ofNat spender.toNat))).insert
    "_value" (.int (Int.ofNat value.toNat))
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_addr_uint256_ok hargs hcanon
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  have rd5959 := vaultBlocks.vault_block_5947_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_5959_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
      (by native_decide) rd5959
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5959_taken_stack]) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) evm locals (approveTransition.body.drop 2) hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have rd5971 := vaultBlocks.vault_block_5959_fallthrough (by simp)
    (u256_eq_of_ne (Ne.symm hlocked)) rd5959
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have rd5973 := rd5971.push1 (UInt256.ofNat 1) (by native_decide)
      (by simp [vaultBlocks.vault_block_5959_fallthrough_stack])
    have rd5974 := rd5973.push0 (by native_decide)
      (by simp [vaultBlocks.vault_block_5959_fallthrough_stack])
    have hstatic := tstoreStaticReach rd5974 hp (by native_decide)
      (by simp [vaultBlocks.vault_block_5959_fallthrough_stack])
    have hsource := vaultMutatingBodyStatic (fork := fork) evm locals (approveTransition.body.drop 3) hvalue
      (by rw [hload]; exact hlocked) hp
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  have hsLocked : SourceState evm I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) (vaultSetLock evm ⟨1⟩) :=
    sourceStateTransientWrite SourceState.init ⟨0⟩ ⟨1⟩
  have rd7939 := vaultBlocks.vault_block_5971 (by simp [vaultBlocks.vault_block_5959_fallthrough_stack])
    hperm (by native_decide) rd5971
  let mem := spender.toByteArray.write 0 (vaultDispatchMemory ⟨157198259⟩) 192 32
  let owner := UInt256.ofNat I.source.val
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsizeMem : 224 ≤ mem.size := toByteArray_write_size_ge_off_add32 _ _ 192 (hgap _ (by omega) _)
  have hspender : memLoad (UInt256.ofNat 192) (owner.toByteArray.write 0 mem 64 32) = spender := by
    rw [memLoad_above_write _ _ 64 192 (by rw [toByteArray_size]) (by omega) (by omega) hsizeMem (by decide +kernel)]
    exact memLoad_write_back _ _ 192 (by decide +kernel) (hgap _ (by omega) _)
  change RD fork vaultBytecode I (Sat256.ofUInt256 g) evm (UInt256.ofNat 7939) (UInt256.ofNat 5998 :: _)
    (value.toByteArray.write 0 ((memLoad (UInt256.ofNat 192) (owner.toByteArray.write 0 mem 64 32)).toByteArray.write 0
      (owner.toByteArray.write 0 mem 64 32) 96 32) 128 32) _ _ _ _ _ at rd7939
  rw [hspender] at rd7939
  have hownerCanon : owner.toNat < EVM.addressModulus := addressWord_canonical I.source
  have hownerAddr : AccountAddress.ofNat owner.toNat = I.source := addressWord_roundtrip I.source
  obtain ⟨hsizeArgs, hmo, hms, hmv⟩ := vaultApproveArguments_reads mem owner spender value
  obtain ⟨evm', σ', aw', k', C', hcallee, hs', rd5998⟩ := vaultApproveRoutine hsLocked
    hsizeArgs hmo hms hmv hownerCanon hcanon hperm
    (by simp [vaultBlocks.vault_block_5959_fallthrough_stack]) (by native_decide) rd7939
  rw [hownerAddr] at hcallee
  have henvLocked : (vaultSetLock evm ⟨1⟩).executionEnv = I := hsLocked.env
  have hcallee' := vaultApprovePublicReturns (evm := vaultSetLock evm ⟨1⟩) (evm' := evm')
    (spender := AccountAddress.ofNat spender.toNat) (value := value)
    (by simpa only [henvLocked] using hcallee)
  have hsource := vaultMutatingBodyReturns (hpermAfter := (congrArg ExecutionEnv.perm hs'.env).trans hperm) (hperm := by assumption) (fn := vaultApprovePublicFunction) (locals := locals)
    (args := [.var "_spender", .var "_value"])
    (argVals := [.address (AccountAddress.ofNat spender.toNat), .int (Int.ofNat value.toNat)])
    hvalue (by rw [hload]; exact hlocked)
    (by simp only [evalExprs?, evalExpr?, locals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.bind, pure, bind]; rfl) rfl rfl hcallee'
  have hret := vaultBlocks.vault_block_5998 (by simp [vaultBlocks.vault_block_5959_fallthrough_stack]) hperm rd5998
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) evm (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
    (((⟨1⟩ : UInt256).toByteArray.write 0 _ 224 32).readWithPadding 224 32) at hret
  rw [toByteArray_write_read_back_of_gap _ _ _ (hgap _ (by omega) _)] at hret
  have hsFinal : SourceState evm I (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (vaultSetLock evm' ⟨0⟩) := by
    unfold vaultSetLock
    rw [hs'.env]
    exact sourceStateTransientWrite hs' ⟨0⟩ ⟨0⟩
  exact hret.reEquivExecutionGen hcode hd hdec hsource hsFinal.accounts
    (returnEquiv_of_encode boolTrueReturnEncoding)

theorem vaultApproveBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultApproveBodyCore hcode hsize hsel
end Benchmarks.CurveVault
