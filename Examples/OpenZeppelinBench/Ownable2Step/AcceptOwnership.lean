import Examples.OpenZeppelinBench.Ownable2Step.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## `acceptOwnership()` -/

def acceptOwnershipSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def acceptOwnershipPendingOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def acceptOwnershipOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev acceptOwnershipPendingOwnerAddressWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (acceptOwnershipPendingOwnerWord σ I) solcAddrMask

def acceptOwnershipClearPendingWord (old : UInt256) : UInt256 :=
  ownable2StepSetAddressWord old ⟨0⟩

def acceptOwnershipAfterPendingMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩
    (acceptOwnershipClearPendingWord (acceptOwnershipPendingOwnerWord σ I))

def acceptOwnershipOwnerWordAfterPending (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  acceptOwnershipAfterPendingMap σ I |>.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def acceptOwnershipSetOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  ownable2StepSetAddressWord (acceptOwnershipOwnerWordAfterPending σ I)
    (acceptOwnershipSourceWord I)

def acceptOwnershipAfterOwnerMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (acceptOwnershipAfterPendingMap σ I) ⟨0⟩
    (acceptOwnershipSetOwnerWord σ I)

def acceptOwnershipAfterPendingState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (acceptOwnershipClearPendingWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩))

def acceptOwnershipAfterOwnerState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (acceptOwnershipAfterPendingState evm)
    (acceptOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩
    (ownable2StepSetAddressWord
      (Solm.EVM.storageLoad (acceptOwnershipAfterPendingState evm)
        (acceptOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩)
      (UInt256.ofNat (acceptOwnershipAfterPendingState evm).executionEnv.source.val))

theorem acceptOwnershipSourceWord_toNat (I : ExecutionEnv) :
    (acceptOwnershipSourceWord I).toNat = I.source.val := by
  unfold acceptOwnershipSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem acceptOwnershipSourceWord_canonical (I : ExecutionEnv) :
    (acceptOwnershipSourceWord I).toNat < EVM.addressModulus := by
  rw [acceptOwnershipSourceWord_toNat]
  exact I.source.isLt

theorem acceptOwnershipSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (acceptOwnershipSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [acceptOwnershipSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem acceptOwnershipMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = acceptOwnershipSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, acceptOwnershipSource_ofNat]

theorem acceptOwnershipWord_eq_of_maskedAddress_eq_source {w : UInt256} {I : ExecutionEnv}
    (h : AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source) :
    UInt256.land w solcAddrMask = acceptOwnershipSourceWord I := by
  apply u256_inj
  have hcanon := solcAddrMask_result_canonical w
  have hval := congrArg Fin.val h
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [acceptOwnershipSourceWord_toNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  exact hval

theorem acceptOwnershipSetAddressZero_eq (old : UInt256) :
    acceptOwnershipClearPendingWord old =
      UInt256.land old (UInt256.lnot solcAddrMask) := by
  unfold acceptOwnershipClearPendingWord
  apply u256_inj
  rw [ownable2StepSetAddressWord_toNat old ⟨0⟩ (by decide),
    ownable2StepHigh160Mask_toNat]
  simp

theorem acceptOwnershipAfterPendingState_accountMap (evm : EVM.State) :
    (acceptOwnershipAfterPendingState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨1⟩
        (acceptOwnershipClearPendingWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)) := by
  simp [acceptOwnershipAfterPendingState, ownable2StepStorageStore_accountMap]

theorem acceptOwnershipAfterPendingState_createdAccounts (evm : EVM.State) :
    (acceptOwnershipAfterPendingState evm).createdAccounts = evm.createdAccounts := by
  simp [acceptOwnershipAfterPendingState, ownable2StepStorageStore_createdAccounts]

theorem acceptOwnershipAfterPendingState_executionEnv (evm : EVM.State) :
    (acceptOwnershipAfterPendingState evm).executionEnv = evm.executionEnv := by
  simp [acceptOwnershipAfterPendingState, storageStore_executionEnv]

theorem acceptOwnershipAfterOwnerState_accountMap (evm : EVM.State) :
    (acceptOwnershipAfterOwnerState evm).accountMap =
      sstoreAccountMap (acceptOwnershipAfterPendingState evm).executionEnv.codeOwner
        (acceptOwnershipAfterPendingState evm).accountMap ⟨0⟩
        (ownable2StepSetAddressWord
          (Solm.EVM.storageLoad (acceptOwnershipAfterPendingState evm)
            (acceptOwnershipAfterPendingState evm).executionEnv.codeOwner ⟨0⟩)
          (UInt256.ofNat (acceptOwnershipAfterPendingState evm).executionEnv.source.val)) := by
  simp [acceptOwnershipAfterOwnerState, ownable2StepStorageStore_accountMap]

theorem acceptOwnershipAfterOwnerState_createdAccounts (evm : EVM.State) :
    (acceptOwnershipAfterOwnerState evm).createdAccounts =
      (acceptOwnershipAfterPendingState evm).createdAccounts := by
  simp [acceptOwnershipAfterOwnerState, ownable2StepStorageStore_createdAccounts]

theorem acceptOwnershipAfterOwnerState_executionEnv (evm : EVM.State) :
    (acceptOwnershipAfterOwnerState evm).executionEnv =
      (acceptOwnershipAfterPendingState evm).executionEnv := by
  simp [acceptOwnershipAfterOwnerState, storageStore_executionEnv]

theorem evalExpr_acceptOwnership_pendingOwner (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.storage pendingOwnerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pendingOwnerRef = .ok { base := "_pendingOwner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pendingOwnerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_pendingOwner", steps := [] } : EvaledStorageRef) =
      some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp) (her := her)
    (hty := hty) (hloc := by rfl), ownable2StepStorageLocLoad_address_offset0]

theorem evalExpr_acceptOwnership_sender (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_acceptOwnership_pendingOwner_eq_true (evm : EVM.State)
    (h :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) solcAddrMask =
        UInt256.ofNat evm.executionEnv.source.val) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage pendingOwnerRef) sender) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_acceptOwnership_pendingOwner, evalExpr_acceptOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [acceptOwnershipMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) h]
  simp [BEq.beq]

theorem evalExpr_acceptOwnership_pendingOwner_eq_false (evm : EVM.State)
    (h :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) solcAddrMask ≠
        UInt256.ofNat evm.executionEnv.source.val) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage pendingOwnerRef) sender) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_acceptOwnership_pendingOwner, evalExpr_acceptOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask).toNat ≠ evm.executionEnv.source := by
    intro haddr
    exact h (acceptOwnershipWord_eq_of_maskedAddress_eq_source haddr)
  rw [show ((.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask).toNat) : Value) == .address evm.executionEnv.source) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_acceptOwnership_zeroAddr (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure, bind]

theorem evalExpr_acceptOwnership_sender_afterPending (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ }
      (acceptOwnershipAfterPendingState evm) sender =
        .ok (.address (acceptOwnershipAfterPendingState evm).executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem acceptOwnershipAssignPending (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage pendingOwnerRef
        (.address (AccountAddress.ofNat 0)) =
      .ok ({ contract := contract, locals := ∅ }, acceptOwnershipAfterPendingState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pendingOwnerRef = .ok { base := "_pendingOwner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pendingOwnerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_pendingOwner", steps := [] } : EvaledStorageRef) =
      some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (addrLoc ⟨1⟩) (.address (AccountAddress.ofNat 0)) =
        some (acceptOwnershipAfterPendingState evm) := by
    simpa [acceptOwnershipAfterPendingState, acceptOwnershipClearPendingWord] using
      ownable2StepStorageLocStore_address_offset0 evm ⟨1⟩ ⟨0⟩ (by decide)
  exact assignStorageRef_storage_scalar_value (cfg := config) (solm := { contract := contract, locals := ∅ })
    (evm := evm) (evm' := acceptOwnershipAfterPendingState evm) (slot := pendingOwnerRef)
    (er := { base := "_pendingOwner", steps := [] }) (ty := .elem .address)
    (loc := addrLoc ⟨1⟩) (value := .address (AccountAddress.ofNat 0))
    (by simp) her hty (by rfl) (by trivial) hstore

theorem acceptOwnershipAssignOwner (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ }
        (acceptOwnershipAfterPendingState evm) .storage ownerRef
        (.address (acceptOwnershipAfterPendingState evm).executionEnv.source) =
      .ok ({ contract := contract, locals := ∅ }, acceptOwnershipAfterOwnerState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ }
      (acceptOwnershipAfterPendingState evm) ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore (acceptOwnershipAfterPendingState evm) (addrLoc ⟨0⟩)
          (.address (acceptOwnershipAfterPendingState evm).executionEnv.source) =
        some (acceptOwnershipAfterOwnerState evm) := by
    have hsource :
        AccountAddress.ofNat
            (UInt256.ofNat (acceptOwnershipAfterPendingState evm).executionEnv.source.val).toNat =
          (acceptOwnershipAfterPendingState evm).executionEnv.source := by
      simpa using acceptOwnershipSource_ofNat (acceptOwnershipAfterPendingState evm).executionEnv
    rw [← hsource]
    simpa [acceptOwnershipAfterOwnerState] using
      ownable2StepStorageLocStore_address_offset0 (acceptOwnershipAfterPendingState evm) ⟨0⟩
        (UInt256.ofNat (acceptOwnershipAfterPendingState evm).executionEnv.source.val)
        (ownable2StepSourceWord_canonical (acceptOwnershipAfterPendingState evm).executionEnv)
  exact assignStorageRef_storage_scalar_value (cfg := config) (solm := { contract := contract, locals := ∅ })
    (evm := acceptOwnershipAfterPendingState evm)
    (evm' := acceptOwnershipAfterOwnerState evm) (slot := ownerRef)
    (er := { base := "_owner", steps := [] }) (ty := .elem .address)
    (loc := addrLoc ⟨0⟩)
    (value := .address (acceptOwnershipAfterPendingState evm).executionEnv.source)
    (by simp) her hty (by rfl) (by trivial) hstore

theorem ownable2StepAcceptOwnershipBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpending :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) solcAddrMask =
        UInt256.ofNat evm.executionEnv.source.val) :
    ExecTransitionBody config contract evm ∅ acceptOwnershipTransition.body
      (.returned { contract := contract, locals := ∅ } (acceptOwnershipAfterOwnerState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_acceptOwnership_pendingOwner_eq_true evm hpending)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_acceptOwnership_zeroAddr evm) (acceptOwnershipAssignPending evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_acceptOwnership_sender_afterPending evm)
      (acceptOwnershipAssignOwner evm)) ?_
  exact ExecBlock.nil

theorem ownable2StepAcceptOwnershipBodyReverts_pendingOwner (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpending :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) solcAddrMask ≠
        UInt256.ofNat evm.executionEnv.source.val) :
    ExecTransitionBody config contract evm ∅ acceptOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_acceptOwnership_pendingOwner_eq_false evm hpending))

set_option maxHeartbeats 1000000 in
theorem ownable2StepX_acceptOwnership_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hpending :
      UInt256.land (acceptOwnershipPendingOwnerWord σ I) solcAddrMask =
        ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨99⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, acceptOwnershipAfterOwnerMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd99⟩ := hreach
  have rd202 := evm_run rd99 with [jumpdest, push2 ⟨97⟩, push2 ⟨202⟩, jump (by jump_dest)]
  have rd203 := evm_run rd202 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd206₀⟩ := rd203.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd206⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [acceptOwnershipPendingOwnerWord σ I, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [acceptOwnershipPendingOwnerWord] using rd206₀⟩
  have rd219₀ := evm_run rd206 with [
    caller, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2, eq]
  have hmask :
      UInt256.land solcAddrMask (acceptOwnershipPendingOwnerWord σ I) =
        ownable2StepSourceWord I := by
    rw [Reasoning.Theory.u256_land_comm, hpending]
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (acceptOwnershipPendingOwnerWord σ I)) = ⟨1⟩ := by
    change UInt256.eq (ownable2StepSourceWord I)
      (UInt256.land solcAddrMask (acceptOwnershipPendingOwnerWord σ I)) = ⟨1⟩
    rw [hmask, u256_eq_refl]
  have rd219 := rd219₀
  rw [heq] at rd219
  have rd263 := evm_run rd219 with [push2 ⟨263⟩, jumpiT (by decide) (by jump_dest)]
  have rd431 := evm_run rd263 with [jumpdest, push2 ⟨272⟩, dup2, push2 ⟨431⟩,
    jump (by jump_dest)]
  have rd435 := evm_run rd431 with [jumpdest, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd436₀⟩ := rd435.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd436⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨436⟩
      [acceptOwnershipPendingOwnerWord σ I, ⟨1⟩, ownable2StepSourceWord I, ⟨272⟩,
        ownable2StepSourceWord I, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [acceptOwnershipPendingOwnerWord, ownable2StepSourceWord] using rd436₀⟩
  have rd446₀ := evm_run rd436 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and]
  have hclear :
      UInt256.land (UInt256.lnot solcAddrMask) (acceptOwnershipPendingOwnerWord σ I) =
        acceptOwnershipClearPendingWord (acceptOwnershipPendingOwnerWord σ I) := by
    rw [Reasoning.Theory.u256_land_comm]
    exact (acceptOwnershipSetAddressZero_eq (acceptOwnershipPendingOwnerWord σ I)).symm
  have rd446 := rd446₀
  rw [show UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        UInt256.lnot solcAddrMask by decide] at rd446
  rw [hclear] at rd446
  have rd447 := evm_run rd446 with [swap1]
  obtain ⟨_, _, rd448₀⟩ := rd447.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd448⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨448⟩
      [ownable2StepSourceWord I, ⟨272⟩, ownable2StepSourceWord I, ⟨97⟩,
        ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, acceptOwnershipAfterPendingMap σ I) k C := by
    exact ⟨_, _, by
      simpa [acceptOwnershipAfterPendingMap] using rd448₀⟩
  let σp := acceptOwnershipAfterPendingMap σ I
  have rd454 := evm_run rd448 with [push2 ⟨272⟩, dup2, push0, dup1]
  obtain ⟨_, _, rd455₀⟩ := rd454.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd455⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨455⟩
      [acceptOwnershipOwnerWordAfterPending σ I, ⟨0⟩, ownable2StepSourceWord I, ⟨272⟩,
        ownable2StepSourceWord I, ⟨272⟩, ownable2StepSourceWord I, ⟨97⟩,
        ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σp) k C := by
    exact ⟨_, _, by simpa [σp, acceptOwnershipOwnerWordAfterPending] using rd455₀⟩
  have rd478 := evm_run rd455 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2]
  have rd479₀ := RD.lor rd478 (by decide) (by evm_ov)
  have rd480₀ := evm_run rd479₀ with [dup5]
  have hset :
      UInt256.lor
          (UInt256.land solcAddrMask (ownable2StepSourceWord I))
          (UInt256.land (acceptOwnershipOwnerWordAfterPending σ I) (UInt256.lnot solcAddrMask)) =
        acceptOwnershipSetOwnerWord σ I := by
    unfold acceptOwnershipSetOwnerWord ownable2StepSetAddressWord acceptOwnershipSourceWord
      ownable2StepSourceWord
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (UInt256.ofNat I.source.val)]
    rw [u256_lor_comm]
  have rd480 := rd480₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by decide] at rd480
  rw [hset] at rd480
  obtain ⟨_, _, rd481₀⟩ := rd480.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd481⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨481⟩
      [UInt256.land solcAddrMask (ownable2StepSourceWord I), solcAddrMask,
        acceptOwnershipOwnerWordAfterPending σ I, ⟨0⟩, ownable2StepSourceWord I, ⟨272⟩,
        ownable2StepSourceWord I, ⟨272⟩, ownable2StepSourceWord I, ⟨97⟩,
        ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, acceptOwnershipAfterOwnerMap σ I) k C := by
    exact ⟨_, _, by
      simpa [acceptOwnershipAfterOwnerMap, σp] using rd481₀⟩
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
  have rd97 := evm_run rd272 with [jumpdest, pop, jump (by jump_dest)]
  have rd98 := evm_run rd97 with [jumpdest]
  exact rd98.stop (by decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem ownable2StepX_acceptOwnership_revert_pendingOwner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpending :
      UInt256.land (acceptOwnershipPendingOwnerWord σ I) solcAddrMask ≠
        ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨99⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd99⟩ := hreach
  have rd202 := evm_run rd99 with [jumpdest, push2 ⟨97⟩, push2 ⟨202⟩, jump (by jump_dest)]
  have rd203 := evm_run rd202 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd206₀⟩ := rd203.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd206⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [acceptOwnershipPendingOwnerWord σ I, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [acceptOwnershipPendingOwnerWord] using rd206₀⟩
  have rd219₀ := evm_run rd206 with [
    caller, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2, eq]
  have hmask :
      UInt256.land solcAddrMask (acceptOwnershipPendingOwnerWord σ I) ≠
        ownable2StepSourceWord I := by
    intro h
    exact hpending (by rw [Reasoning.Theory.u256_land_comm] at h; exact h)
  have hneq :
      UInt256.ofNat I.source.val ≠
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (acceptOwnershipPendingOwnerWord σ I) := by
    change ownable2StepSourceWord I ≠
      UInt256.land solcAddrMask (acceptOwnershipPendingOwnerWord σ I)
    exact fun h => hmask h.symm
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (acceptOwnershipPendingOwnerWord σ I)) = ⟨0⟩ := by
    exact u256_eq_of_ne hneq
  have rd219 := rd219₀
  rw [heq] at rd219
  have rd223 := evm_run rd219 with [push2 ⟨263⟩, jumpiNT (by decide)]
  have rd236 := evm_run rd223 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x118cdaa7⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem ownable2StepUnauthorizedSelector) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd253 := evm_run rd236 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, push1 ⟨4⟩, dup3,
    add]
  have rd254₀ := evm_run rd253 with [
    raw mstore 3 (ownable2StepUnauthorizedMem (ownable2StepSourceWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide]
        rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        rw [Reasoning.Theory.u256_land_comm (UInt256.ofNat I.source.val) solcAddrMask]
        simp [ownable2StepUnauthorizedMem, ownable2StepSourceWord])
      (by decide) (by evm_ov),
    push1 ⟨36⟩, add]
  have rd262 := evm_run rd254₀ with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (ownable2StepUnauthorizedMem_mload64 (ownable2StepSourceWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd262.rev 0 (by decide) mem_cost (by evm_ov)

theorem ownable2StepAcceptOwnershipSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x79, 0xba, 0x50, 0x97]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x79, 0xba, 0x50, 0x97]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ownable2StepDispatch_acceptOwnership {cd : ByteArray}
    (hsel : ((⟨#[0x79, 0xba, 0x50, 0x97]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some acceptOwnershipTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [ownerTransition, pendingOwnerTransition, renounceOwnershipTransition,
      transferOwnershipTransition])
    rfl rfl ?_ (by rw [selectorOf, acceptOwnershipSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem ownable2StepDecode_acceptOwnership {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (acceptOwnershipTransition.params.map Param.name)
      (transitionSignature acceptOwnershipTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem ownable2StepAcceptOwnershipBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x79, 0xba, 0x50, 0x97]⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨99⟩
      [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := ownable2StepAcceptOwnershipSelector_size hsel
  have hd := ownable2StepDispatch_acceptOwnership (cd := I.calldata) hsel
  have hdec := ownable2StepDecode_acceptOwnership (I := I) hsz
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
  have hpendWord :
      acceptOwnershipPendingOwnerWord σ_evm I = acceptOwnershipPendingOwnerWord σ_solm I := by
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  by_cases hpending :
      UInt256.land (acceptOwnershipPendingOwnerWord σ_evm I) solcAddrMask =
        ownable2StepSourceWord I
  · have hpendingSolm :
        UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨1⟩) solcAddrMask =
          UInt256.ofNat evmS.executionEnv.source.val := by
      have hmap :
          UInt256.land (acceptOwnershipPendingOwnerWord σ_solm I) solcAddrMask =
            ownable2StepSourceWord I := by
        simpa [hpendWord] using hpending
      simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
        acceptOwnershipPendingOwnerWord, ownable2StepSourceWord] using hmap
    have hbody := ownable2StepAcceptOwnershipBodyReturns evmS
      (by simp only [evmS, initState]; exact hwv) hpendingSolm
    have hPendingVal :
        acceptOwnershipClearPendingWord
            (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨1⟩) =
          acceptOwnershipClearPendingWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨1⟩) := by
      rw [hσ.storageLoad_codeOwner ⟨1⟩]
    have hσPending : EVMStateEquiv
        (acceptOwnershipAfterPendingState evmE) (acceptOwnershipAfterPendingState evmS) := by
      simpa [acceptOwnershipAfterPendingState] using hσ.storageStore_codeOwner ⟨1⟩ hPendingVal
    have hSource :
        UInt256.ofNat (acceptOwnershipAfterPendingState evmE).executionEnv.source.val =
          UInt256.ofNat (acceptOwnershipAfterPendingState evmS).executionEnv.source.val := by
      rw [acceptOwnershipAfterPendingState_executionEnv,
        acceptOwnershipAfterPendingState_executionEnv, hσ.executionEnv]
    have hOwnerVal :
        ownable2StepSetAddressWord
            (Solm.EVM.storageLoad (acceptOwnershipAfterPendingState evmE)
              (acceptOwnershipAfterPendingState evmE).executionEnv.codeOwner ⟨0⟩)
            (UInt256.ofNat (acceptOwnershipAfterPendingState evmE).executionEnv.source.val) =
          ownable2StepSetAddressWord
            (Solm.EVM.storageLoad (acceptOwnershipAfterPendingState evmS)
              (acceptOwnershipAfterPendingState evmS).executionEnv.codeOwner ⟨0⟩)
            (UInt256.ofNat (acceptOwnershipAfterPendingState evmS).executionEnv.source.val) := by
      exact congrArg₂ ownable2StepSetAddressWord
        (hσPending.storageLoad_codeOwner ⟨0⟩) hSource
    have hσPost : EVMStateEquiv
        (acceptOwnershipAfterOwnerState evmE) (acceptOwnershipAfterOwnerState evmS) := by
      simpa [acceptOwnershipAfterOwnerState] using
        hσPending.storageStore_codeOwner ⟨0⟩ hOwnerVal
    exact (ownable2StepX_acceptOwnership_success (g := Sat256.ofUInt256 g)
        hperm hpending hreach)
      |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
        (by
          rw [acceptOwnershipAfterOwnerState_createdAccounts,
            acceptOwnershipAfterPendingState_createdAccounts]
          simp [evmE, initState])
        (accountMapEquiv.of_eq (by
          rw [acceptOwnershipAfterOwnerState_accountMap, acceptOwnershipAfterPendingState_accountMap]
          simp [evmE, initState, acceptOwnershipAfterOwnerMap, acceptOwnershipAfterPendingMap,
            acceptOwnershipPendingOwnerWord, acceptOwnershipOwnerWordAfterPending,
            acceptOwnershipSetOwnerWord, acceptOwnershipAfterPendingState_accountMap,
            acceptOwnershipAfterPendingState_executionEnv, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage, acceptOwnershipSourceWord]))
        hσPost
        (returnEquiv.void rfl rfl rfl)
  · have hpendingSolm :
        UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨1⟩) solcAddrMask ≠
          UInt256.ofNat evmS.executionEnv.source.val := by
      intro h
      apply hpending
      have hmap :
          UInt256.land (acceptOwnershipPendingOwnerWord σ_solm I) solcAddrMask =
            ownable2StepSourceWord I := by
        simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
          acceptOwnershipPendingOwnerWord, ownable2StepSourceWord] using h
      simpa [hpendWord] using hmap
    have hbody := ownable2StepAcceptOwnershipBodyReverts_pendingOwner evmS
      (by simp only [evmS, initState]; exact hwv) hpendingSolm
    exact (ownable2StepX_acceptOwnership_revert_pendingOwner (g := Sat256.ofUInt256 g)
        hpending hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Ownable2Step
