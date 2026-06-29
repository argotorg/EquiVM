import Examples.OpenZeppelinBench.AccessControl.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `DEFAULT_ADMIN_ROLE()` proof

The body is a zero-argument getter returning the constant zero `bytes32`.
-/

abbrev defaultAdminRoleWord : UInt256 :=
  ⟨0⟩

abbrev defaultAdminRoleValue : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE defaultAdminRoleWord)

theorem defaultAdminRole_zeroBytes :
    (List.replicate 32 0 : List UInt8) = EVM.Word.toBytesBE defaultAdminRoleWord := by
  native_decide

theorem accessControlDefaultAdminRoleSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_defaultAdminRole {cd : ByteArray}
    (hsel : ((⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some defaultAdminRoleTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [getRoleAdminTransition, grantRoleTransition, hasRoleTransition,
      renounceRoleTransition, revokeRoleTransition, supportsInterfaceTransition])
    rfl rfl ?_ (by rw [selectorOf, defaultAdminRoleSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem accessControlDecode_defaultAdminRole {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (defaultAdminRoleTransition.params.map Param.name)
      (transitionSignature defaultAdminRoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem accessControlDefaultAdminRoleBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ defaultAdminRoleTransition.body
      (.returned { contract := contract, locals := ∅ } evm (some defaultAdminRoleValue)) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [defaultAdminRoleValue, defaultAdminRole, defaultAdminRole_zeroBytes]
      simp [evalExpr?, pure])

abbrev accessControlDefaultAdminRoleRetEnd : UInt256 :=
  (⟨32⟩ : UInt256) + ⟨128⟩

theorem accessControlDefaultAdminRoleSubRet32_toNat :
    (UInt256.sub accessControlDefaultAdminRoleRetEnd ⟨128⟩).toNat = 32 := by
  decide

theorem accessControlX_defaultAdminRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨273⟩ [accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray defaultAdminRoleWord) := by
  obtain ⟨_, _, rd273⟩ := hreach
  have rd200 := evm_run rd273 with [
    jumpdest, push2 ⟨200⟩, push0, dup2, jump (by jump_dest) ]
  have rd157 := evm_run rd200 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem defaultAdminRoleWord) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨157⟩, jump (by jump_dest) ]
  exact evm_run rd157 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 defaultAdminRoleWord)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray defaultAdminRoleWord) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          accessControlDefaultAdminRoleSubRet32_toNat]
        simpa using solcReturnMem_read128 defaultAdminRoleWord)
      (by evm_ov) ]

theorem accessControlDefaultAdminRoleBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨273⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := accessControlDefaultAdminRoleSelector_size hsel
  have hd := accessControlDispatch_defaultAdminRole (cd := I.calldata) (by
    simpa [selIs] using hsel)
  have hdec := accessControlDecode_defaultAdminRole (I := I) hsz
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        defaultAdminRoleTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some defaultAdminRoleValue)) := by
    exact accessControlDefaultAdminRoleBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (accessControlX_defaultAdminRole (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody rfl hAccounts
      (returnEquiv_of_encode (by
        simpa [bytes32] using bytes32ReturnEncoding defaultAdminRoleWord))

end OpenZeppelinBench.AccessControl
