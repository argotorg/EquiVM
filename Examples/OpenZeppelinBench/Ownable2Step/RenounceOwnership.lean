import Examples.OpenZeppelinBench.Ownable2Step.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## `renounceOwnership()` -/

def renounceOwnershipOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def renounceOwnershipPendingOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

abbrev renounceOwnershipOwnerAddressWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (renounceOwnershipOwnerWord σ I) solcAddrMask

def renounceOwnershipClearAddressWord (old : UInt256) : UInt256 :=
  ownable2StepSetAddressWord old ⟨0⟩

def renounceOwnershipAfterPendingMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩
    (renounceOwnershipClearAddressWord (renounceOwnershipPendingOwnerWord σ I))

def renounceOwnershipOwnerWordAfterPending (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  renounceOwnershipAfterPendingMap σ I |>.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def renounceOwnershipSetOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  renounceOwnershipClearAddressWord (renounceOwnershipOwnerWordAfterPending σ I)

def renounceOwnershipAfterOwnerMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (renounceOwnershipAfterPendingMap σ I) ⟨0⟩
    (renounceOwnershipSetOwnerWord σ I)

def renounceOwnershipAfterPendingState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (renounceOwnershipClearAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩))

def renounceOwnershipAfterOwnerState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (renounceOwnershipAfterPendingState evm)
    (renounceOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩
    (renounceOwnershipClearAddressWord
      (Solm.EVM.storageLoad (renounceOwnershipAfterPendingState evm)
        (renounceOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩))

theorem renounceOwnershipSetAddressZero_eq (old : UInt256) :
    renounceOwnershipClearAddressWord old =
      UInt256.land old (UInt256.lnot solcAddrMask) := by
  unfold renounceOwnershipClearAddressWord
  apply u256_inj
  rw [ownable2StepSetAddressWord_toNat old ⟨0⟩ (by decide),
    ownable2StepHigh160Mask_toNat]
  simp

theorem renounceOwnershipU256_lor_zero (a : UInt256) :
    UInt256.lor a ⟨0⟩ = a := by
  apply u256_inj
  change Nat.lor a.toNat 0 % UInt256.size = a.toNat
  have hlor : Nat.lor a.toNat 0 = a.toNat := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    change Nat.testBit (a.toNat ||| 0) i = Nat.testBit a.toNat i
    rw [Nat.testBit_lor]
    simp
  have hlt : a.toNat < UInt256.size := by
    exact a.val.isLt
  rw [hlor, Nat.mod_eq_of_lt hlt]

theorem renounceOwnershipAfterPendingState_accountMap (evm : EVM.State) :
    (renounceOwnershipAfterPendingState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨1⟩
        (renounceOwnershipClearAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)) := by
  simp [renounceOwnershipAfterPendingState, ownable2StepStorageStore_accountMap]

theorem renounceOwnershipAfterPendingState_createdAccounts (evm : EVM.State) :
    (renounceOwnershipAfterPendingState evm).createdAccounts = evm.createdAccounts := by
  simp [renounceOwnershipAfterPendingState, ownable2StepStorageStore_createdAccounts]

theorem renounceOwnershipAfterPendingState_executionEnv (evm : EVM.State) :
    (renounceOwnershipAfterPendingState evm).executionEnv = evm.executionEnv := by
  simp [renounceOwnershipAfterPendingState, storageStore_executionEnv]

theorem renounceOwnershipAfterOwnerState_accountMap (evm : EVM.State) :
    (renounceOwnershipAfterOwnerState evm).accountMap =
      sstoreAccountMap (renounceOwnershipAfterPendingState evm).executionEnv.codeOwner
        (renounceOwnershipAfterPendingState evm).accountMap ⟨0⟩
        (renounceOwnershipClearAddressWord
          (Solm.EVM.storageLoad (renounceOwnershipAfterPendingState evm)
            (renounceOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩)) := by
  simp [renounceOwnershipAfterOwnerState, ownable2StepStorageStore_accountMap]

theorem renounceOwnershipAfterOwnerState_createdAccounts (evm : EVM.State) :
    (renounceOwnershipAfterOwnerState evm).createdAccounts =
      (renounceOwnershipAfterPendingState evm).createdAccounts := by
  simp [renounceOwnershipAfterOwnerState, ownable2StepStorageStore_createdAccounts]

theorem renounceOwnershipAfterOwnerState_executionEnv (evm : EVM.State) :
    (renounceOwnershipAfterOwnerState evm).executionEnv =
      (renounceOwnershipAfterPendingState evm).executionEnv := by
  simp [renounceOwnershipAfterOwnerState, storageStore_executionEnv]

theorem evalExpr_renounceOwnership_owner (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp) (her := her)
    (hty := hty) (hloc := by rfl), ownable2StepStorageLocLoad_address_offset0]

theorem evalExpr_renounceOwnership_sender (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_renounceOwnership_owner_eq_true (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        ownable2StepSourceWord evm.executionEnv) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage ownerRef) sender) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_renounceOwnership_owner, evalExpr_renounceOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [ownable2StepMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_renounceOwnership_owner_eq_false (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        ownable2StepSourceWord evm.executionEnv) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage ownerRef) sender) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_renounceOwnership_owner, evalExpr_renounceOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat ≠ evm.executionEnv.source := by
    intro haddr
    exact howner (ownable2StepWord_eq_of_maskedAddress_eq_source haddr)
  rw [show ((.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat) : Value) == .address evm.executionEnv.source) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_renounceOwnership_zeroAddr (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure, bind]

theorem evalExpr_renounceOwnership_zeroAddr_afterPending (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ }
      (renounceOwnershipAfterPendingState evm) zeroAddr =
        .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure, bind]

theorem renounceOwnershipAssignPending (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage pendingOwnerRef
        (.address (AccountAddress.ofNat 0)) =
      .ok ({ contract := contract, locals := ∅ }, renounceOwnershipAfterPendingState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pendingOwnerRef = .ok { base := "_pendingOwner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pendingOwnerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_pendingOwner", steps := [] } : EvaledStorageRef) =
      some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (addrLoc ⟨1⟩) (.address (AccountAddress.ofNat 0)) =
        some (renounceOwnershipAfterPendingState evm) := by
    simpa [renounceOwnershipAfterPendingState, renounceOwnershipClearAddressWord] using
      ownable2StepStorageLocStore_address_offset0 evm ⟨1⟩ ⟨0⟩ (by decide)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := ∅ }) (evm := evm)
    (evm' := renounceOwnershipAfterPendingState evm) (slot := pendingOwnerRef)
    (er := { base := "_pendingOwner", steps := [] }) (ty := .elem .address)
    (loc := addrLoc ⟨1⟩) (value := .address (AccountAddress.ofNat 0))
    (by simp) her hty (by rfl) (by trivial) hstore

theorem renounceOwnershipAssignOwner (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ }
        (renounceOwnershipAfterPendingState evm) .storage ownerRef
        (.address (AccountAddress.ofNat 0)) =
      .ok ({ contract := contract, locals := ∅ }, renounceOwnershipAfterOwnerState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ }
      (renounceOwnershipAfterPendingState evm) ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore (renounceOwnershipAfterPendingState evm) (addrLoc ⟨0⟩)
          (.address (AccountAddress.ofNat 0)) =
        some (renounceOwnershipAfterOwnerState evm) := by
    simpa [renounceOwnershipAfterOwnerState, renounceOwnershipClearAddressWord] using
      ownable2StepStorageLocStore_address_offset0 (renounceOwnershipAfterPendingState evm) ⟨0⟩
        ⟨0⟩ (by decide)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := ∅ })
    (evm := renounceOwnershipAfterPendingState evm)
    (evm' := renounceOwnershipAfterOwnerState evm) (slot := ownerRef)
    (er := { base := "_owner", steps := [] }) (ty := .elem .address)
    (loc := addrLoc ⟨0⟩) (value := .address (AccountAddress.ofNat 0))
    (by simp) her hty (by rfl) (by trivial) hstore

theorem ownable2StepRenounceOwnershipBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        ownable2StepSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm ∅ renounceOwnershipTransition.body
      (.returned { contract := contract, locals := ∅ } (renounceOwnershipAfterOwnerState evm)
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_renounceOwnership_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_renounceOwnership_zeroAddr evm)
      (renounceOwnershipAssignPending evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_renounceOwnership_zeroAddr_afterPending evm)
      (renounceOwnershipAssignOwner evm)) ?_
  exact ExecBlock.nil

theorem ownable2StepRenounceOwnershipBodyReverts_owner (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        ownable2StepSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm ∅ renounceOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_renounceOwnership_owner_eq_false evm howner))

theorem ownable2StepRenounceOwnershipSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x71, 0x50, 0x18, 0xa6]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x71, 0x50, 0x18, 0xa6]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ownable2StepDispatch_renounceOwnership {cd : ByteArray}
    (hsel : ((⟨#[0x71, 0x50, 0x18, 0xa6]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some renounceOwnershipTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x71, 0x50, 0x18, 0xa6]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [acceptOwnershipTransition, ownerTransition, pendingOwnerTransition])
    (post := [transferOwnershipTransition]) rfl rfl ?_
    (by rw [selectorOf, renounceOwnershipSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, acceptOwnershipSelectorBytes, hcd]; decide
  · rw [selectorOf, ownerSelectorBytes, hcd]; decide
  · rw [selectorOf, pendingOwnerSelectorBytes, hcd]; decide

theorem ownable2StepDecode_renounceOwnership {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (renounceOwnershipTransition.params.map Param.name)
      (transitionSignature renounceOwnershipTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

set_option maxHeartbeats 1000000 in
theorem ownable2StepX_renounceOwnership_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (howner :
      UInt256.land (renounceOwnershipOwnerWord σ I) solcAddrMask =
        ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨89⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, renounceOwnershipAfterOwnerMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd89⟩ := hreach
  have rd183 := evm_run rd89 with [jumpdest, push2 ⟨97⟩, push2 ⟨183⟩,
    jump (by jump_dest)]
  have rd387 := evm_run rd183 with [jumpdest, push2 ⟨191⟩, push2 ⟨387⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd191⟩ := RD.ownable2StepOnlyOwnerPass
    (ret := ⟨191⟩) (R := [⟨97⟩, ownable2StepSelWord I]) rd387
    (by simpa [Reasoning.Reach.ownable2StepOnlyOwnerWord, renounceOwnershipOwnerWord] using
      howner)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd431 := evm_run rd191 with [jumpdest, push2 ⟨200⟩, push0, push2 ⟨431⟩,
    jump (by jump_dest)]
  have rd435 := evm_run rd431 with [jumpdest, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd436₀⟩ := rd435.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd436⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨436⟩
      [renounceOwnershipPendingOwnerWord σ I, ⟨1⟩, ⟨0⟩, ⟨200⟩, ⟨97⟩,
        ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [renounceOwnershipPendingOwnerWord] using rd436₀⟩
  have rd446₀ := evm_run rd436 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and]
  have hclear :
      UInt256.land (UInt256.lnot solcAddrMask) (renounceOwnershipPendingOwnerWord σ I) =
        renounceOwnershipClearAddressWord (renounceOwnershipPendingOwnerWord σ I) := by
    rw [Reasoning.Theory.u256_land_comm]
    exact (renounceOwnershipSetAddressZero_eq (renounceOwnershipPendingOwnerWord σ I)).symm
  have rd446 := rd446₀
  rw [show UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        UInt256.lnot solcAddrMask by decide] at rd446
  rw [hclear] at rd446
  have rd447 := evm_run rd446 with [swap1]
  obtain ⟨_, _, rd448₀⟩ := rd447.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd448⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨448⟩
      [⟨0⟩, ⟨200⟩, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, renounceOwnershipAfterPendingMap σ I) k C := by
    exact ⟨_, _, by simpa [renounceOwnershipAfterPendingMap] using rd448₀⟩
  let σp := renounceOwnershipAfterPendingMap σ I
  have rd454 := evm_run rd448 with [push2 ⟨272⟩, dup2, push0, dup1]
  obtain ⟨_, _, rd455₀⟩ := rd454.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd455⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨455⟩
      [renounceOwnershipOwnerWordAfterPending σ I, ⟨0⟩, ⟨0⟩, ⟨272⟩, ⟨0⟩,
        ⟨200⟩, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σp) k C := by
    exact ⟨_, _, by simpa [σp, renounceOwnershipOwnerWordAfterPending] using rd455₀⟩
  have rd478 := evm_run rd455 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2]
  have rd479₀ := RD.lor rd478 (by decide) (by evm_ov)
  have rd480₀ := evm_run rd479₀ with [dup5]
  have hset :
      UInt256.lor
          (UInt256.land solcAddrMask (⟨0⟩ : UInt256))
          (UInt256.land (renounceOwnershipOwnerWordAfterPending σ I) (UInt256.lnot solcAddrMask)) =
        renounceOwnershipSetOwnerWord σ I := by
    unfold renounceOwnershipSetOwnerWord
    rw [show UInt256.land solcAddrMask (⟨0⟩ : UInt256) = ⟨0⟩ by decide]
    rw [u256_lor_comm]
    rw [renounceOwnershipU256_lor_zero]
    exact (renounceOwnershipSetAddressZero_eq (renounceOwnershipOwnerWordAfterPending σ I)).symm
  have rd480 := rd480₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by decide] at rd480
  rw [hset] at rd480
  obtain ⟨_, _, rd481₀⟩ := rd480.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd481⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨481⟩
      [UInt256.land solcAddrMask (⟨0⟩ : UInt256), solcAddrMask,
        renounceOwnershipOwnerWordAfterPending σ I, ⟨0⟩, ⟨0⟩, ⟨272⟩, ⟨0⟩,
        ⟨200⟩, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, renounceOwnershipAfterOwnerMap σ I) k C := by
    exact ⟨_, _, by simpa [renounceOwnershipAfterOwnerMap, σp] using rd481₀⟩
  have rd491pre := evm_run rd481 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap2, swap1, swap3, and, swap3, dup4, swap2]
  have rd524 := rd491pre.pushConst
    (⟨0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd526 := evm_run rd524 with [swap2, swap1]
  have rd527 := rd526.log3 0 (UInt256.ofNat 3) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd529 := evm_run rd527 with [pop, pop, jump (by jump_dest)]
  have rd272 := evm_run rd529 with [jumpdest, pop, jump (by jump_dest)]
  have rd200' := evm_run rd272 with [jumpdest, jump (by jump_dest)]
  have rd98 := evm_run rd200' with [jumpdest]
  exact rd98.stop (by decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem ownable2StepX_renounceOwnership_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (howner :
      UInt256.land (renounceOwnershipOwnerWord σ I) solcAddrMask ≠
        ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨89⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd89⟩ := hreach
  have rd183 := evm_run rd89 with [jumpdest, push2 ⟨97⟩, push2 ⟨183⟩,
    jump (by jump_dest)]
  have rd387 := evm_run rd183 with [jumpdest, push2 ⟨191⟩, push2 ⟨387⟩,
    jump (by jump_dest)]
  exact RD.ownable2StepOnlyOwnerRevert
    (ret := ⟨191⟩) (R := [⟨97⟩, ownable2StepSelWord I]) rd387
    (by simpa [Reasoning.Reach.ownable2StepOnlyOwnerWord, renounceOwnershipOwnerWord] using
      howner)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ownable2StepRenounceOwnershipBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x71, 0x50, 0x18, 0xa6]⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨89⟩
      [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := ownable2StepRenounceOwnershipSelector_size hsel
  have hd := ownable2StepDispatch_renounceOwnership (cd := I.calldata) hsel
  have hdec := ownable2StepDecode_renounceOwnership (I := I) hsz
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
  have hownerWord :
      renounceOwnershipOwnerWord σ_evm I = renounceOwnershipOwnerWord σ_solm I := by
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  by_cases howner :
      UInt256.land (renounceOwnershipOwnerWord σ_evm I) solcAddrMask =
        ownable2StepSourceWord I
  · have hownerSolm :
        UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask =
          ownable2StepSourceWord evmS.executionEnv := by
      have hmap :
          UInt256.land (renounceOwnershipOwnerWord σ_solm I) solcAddrMask =
            ownable2StepSourceWord I := by
        simpa [hownerWord] using howner
      simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
        renounceOwnershipOwnerWord, ownable2StepSourceWord] using hmap
    have hbody := ownable2StepRenounceOwnershipBodyReturns evmS
      (by simp only [evmS, initState]; exact hwv) hownerSolm
    have hPendingVal :
        renounceOwnershipClearAddressWord
            (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨1⟩) =
          renounceOwnershipClearAddressWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨1⟩) := by
      rw [hσ.storageLoad_codeOwner ⟨1⟩]
    have hσPending : EVMStateEquiv
        (renounceOwnershipAfterPendingState evmE) (renounceOwnershipAfterPendingState evmS) := by
      simpa [renounceOwnershipAfterPendingState] using
        hσ.storageStore_codeOwner ⟨1⟩ hPendingVal
    have hOwnerVal :
        renounceOwnershipClearAddressWord
            (Solm.EVM.storageLoad (renounceOwnershipAfterPendingState evmE)
              (renounceOwnershipAfterPendingState evmE).executionEnv.codeOwner ⟨0⟩) =
          renounceOwnershipClearAddressWord
            (Solm.EVM.storageLoad (renounceOwnershipAfterPendingState evmS)
              (renounceOwnershipAfterPendingState evmS).executionEnv.codeOwner ⟨0⟩) := by
      exact congrArg renounceOwnershipClearAddressWord
        (hσPending.storageLoad_codeOwner ⟨0⟩)
    have hσPost : EVMStateEquiv
        (renounceOwnershipAfterOwnerState evmE) (renounceOwnershipAfterOwnerState evmS) := by
      simpa [renounceOwnershipAfterOwnerState] using
        hσPending.storageStore_codeOwner ⟨0⟩ hOwnerVal
    exact (ownable2StepX_renounceOwnership_success (g := Sat256.ofUInt256 g)
        hperm howner hreach)
      |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
        (by
          rw [renounceOwnershipAfterOwnerState_createdAccounts,
            renounceOwnershipAfterPendingState_createdAccounts]
          simp [evmE, initState])
        (accountMapEquiv.of_eq (by
          rw [renounceOwnershipAfterOwnerState_accountMap,
            renounceOwnershipAfterPendingState_accountMap]
          simp [evmE, initState, renounceOwnershipAfterOwnerMap,
            renounceOwnershipAfterPendingMap, renounceOwnershipPendingOwnerWord,
            renounceOwnershipOwnerWordAfterPending, renounceOwnershipSetOwnerWord,
            renounceOwnershipAfterPendingState_accountMap,
            renounceOwnershipAfterPendingState_executionEnv, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]))
        hσPost
        (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hownerSolm :
        UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask ≠
          ownable2StepSourceWord evmS.executionEnv := by
      intro h
      apply howner
      have hmap :
          UInt256.land (renounceOwnershipOwnerWord σ_solm I) solcAddrMask =
            ownable2StepSourceWord I := by
        simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
          renounceOwnershipOwnerWord, ownable2StepSourceWord] using h
      simpa [hownerWord] using hmap
    have hbody := ownable2StepRenounceOwnershipBodyReverts_owner evmS
      (by simp only [evmS, initState]; exact hwv) hownerSolm
    exact (ownable2StepX_renounceOwnership_revert_owner (g := Sat256.ofUInt256 g)
        howner hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Ownable2Step
