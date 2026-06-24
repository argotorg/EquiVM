import Examples.Ballot.Common
import Examples.Ballot.Vote
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## `delegate(address)` -/

/-- The raw ABI word for `delegate`'s `to` argument. -/
abbrev delegateToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev delegateToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (delegateToWord I).toNat)

abbrev delegateStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (delegateToValue I)

abbrev delegateSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def delegateSenderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "voters", steps := [.mindex (.address I.source)] }

def delegateSenderFieldRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "voters", steps := [.mindex (.address I.source), .field field] }

def delegateSenderSlot (I : ExecutionEnv) : UInt256 :=
  voterBase (.address I.source)

def delegateSenderPackedSlot (I : ExecutionEnv) : UInt256 :=
  delegateSenderSlot I + ⟨1⟩

def delegateSenderWeightWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (delegateSenderSlot I) ⟨0⟩)

def delegateSenderPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD (delegateSenderPackedSlot I) ⟨0⟩)

abbrev delegateSenderVotedByte (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (delegateSenderPackedWord σ I)

def delegateVoterSlot (w : UInt256) : UInt256 :=
  voterBase (.address (AccountAddress.ofNat w.toNat))

def delegateVoterPackedSlot (w : UInt256) : UInt256 :=
  delegateVoterSlot w + ⟨1⟩

def delegateVoterVoteSlot (w : UInt256) : UInt256 :=
  delegateVoterSlot w + ⟨2⟩

def delegateVoterWeightWord (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (delegateVoterSlot w) ⟨0⟩)

def delegateVoterPackedWord (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD (delegateVoterPackedSlot w) ⟨0⟩)

def delegateVoterVoteWord (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD (delegateVoterVoteSlot w) ⟨0⟩)

abbrev delegateVoterVotedByte (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  UInt256.land ⟨255⟩ (delegateVoterPackedWord σ I w)

abbrev delegateVoterDelegateWord (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask

def delegateSenderPackedStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor ⟨1⟩
    (UInt256.lor
      (UInt256.mul (UInt256.land (delegateToWord I) solcAddrMask) ⟨256⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
        (delegateSenderPackedWord σ I)))

def delegateAfterSenderMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (delegateSenderPackedSlot I)
    (delegateSenderPackedStoreWord σ I)

def delegateUpdatedVoterWeight (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I))
    (delegateSenderWeightWord (delegateAfterSenderMap σ I) I)

def delegateFalseSuccessMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (delegateAfterSenderMap σ I) (delegateVoterSlot (delegateToWord I))
    (delegateUpdatedVoterWeight σ I)

def delegateProposalsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (delegateAfterSenderMap σ I).find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD ⟨2⟩ ⟨0⟩)

def delegateProposalCountSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (⟨1⟩ : UInt256) +
    (UInt256.mul ⟨2⟩
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)) +
      proposalsDataBase)

def delegateProposalCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (delegateAfterSenderMap σ I).find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD (delegateProposalCountSlot σ I) ⟨0⟩)

def delegateUpdatedProposalCount (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (delegateProposalCountWord σ I)
    (delegateSenderWeightWord (delegateAfterSenderMap σ I) I)

def delegateTrueSuccessMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (delegateAfterSenderMap σ I) (delegateProposalCountSlot σ I)
    (delegateUpdatedProposalCount σ I)

theorem delegateSenderWeightWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateSenderWeightWord σ I = delegateSenderWeightWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (delegateSenderSlot I) ⟨0⟩

theorem delegateSenderPackedWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateSenderPackedWord σ I = delegateSenderPackedWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (delegateSenderPackedSlot I) ⟨0⟩

theorem delegateSenderVotedByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateSenderVotedByte σ I = delegateSenderVotedByte τ I := by
  unfold delegateSenderVotedByte
  rw [delegateSenderPackedWord_accountMapEquiv hστ]

theorem delegateVoterWeightWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (w : UInt256) :
    delegateVoterWeightWord σ I w = delegateVoterWeightWord τ I w := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (delegateVoterSlot w) ⟨0⟩

theorem delegateVoterPackedWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (w : UInt256) :
    delegateVoterPackedWord σ I w = delegateVoterPackedWord τ I w := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (delegateVoterPackedSlot w) ⟨0⟩

theorem delegateVoterVoteWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (w : UInt256) :
    delegateVoterVoteWord σ I w = delegateVoterVoteWord τ I w := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (delegateVoterVoteSlot w) ⟨0⟩

theorem delegateVoterVotedByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (w : UInt256) :
    delegateVoterVotedByte σ I w = delegateVoterVotedByte τ I w := by
  unfold delegateVoterVotedByte
  rw [delegateVoterPackedWord_accountMapEquiv hστ w]

theorem delegateVoterDelegateWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (w : UInt256) :
    delegateVoterDelegateWord σ I w = delegateVoterDelegateWord τ I w := by
  unfold delegateVoterDelegateWord
  rw [delegateVoterPackedWord_accountMapEquiv hστ w]

theorem delegateSenderPackedStoreWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateSenderPackedStoreWord σ I = delegateSenderPackedStoreWord τ I := by
  unfold delegateSenderPackedStoreWord
  rw [delegateSenderPackedWord_accountMapEquiv hστ]

theorem delegateAfterSenderMap_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (delegateAfterSenderMap σ I) (delegateAfterSenderMap τ I) := by
  rw [delegateAfterSenderMap, delegateAfterSenderMap,
    delegateSenderPackedStoreWord_accountMapEquiv hστ]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner (delegateSenderPackedSlot I)
    (delegateSenderPackedStoreWord τ I) hστ

-- `delegateUpdatedVoterWeight_accountMapEquiv` / `delegateFalseSuccessMap_accountMapEquiv` were
-- retired when the false-success connect moved to the `EVMStateEquiv` chain
-- (`delegateFalseSuccessState_EVMStateEquiv`), which carries the account-map agreement through the
-- writes; the connect now uses `delegateFalseSuccessState_accountMapEquiv_init` directly on σ_evm.

theorem delegateProposalsLengthWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateProposalsLengthWord σ I = delegateProposalsLengthWord τ I := by
  exact accountMapEquiv_storage_findD (delegateAfterSenderMap_accountMapEquiv (I := I) hστ)
    I.codeOwner ⟨2⟩ ⟨0⟩

theorem delegateProposalCountSlot_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateProposalCountSlot σ I = delegateProposalCountSlot τ I := by
  unfold delegateProposalCountSlot
  rw [delegateVoterVoteWord_accountMapEquiv
    (delegateAfterSenderMap_accountMapEquiv (I := I) hστ) (delegateToWord I)]

theorem delegateProposalCountWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    delegateProposalCountWord σ I = delegateProposalCountWord τ I := by
  unfold delegateProposalCountWord
  rw [delegateProposalCountSlot_accountMapEquiv hστ]
  exact accountMapEquiv_storage_findD (delegateAfterSenderMap_accountMapEquiv (I := I) hστ)
    I.codeOwner (delegateProposalCountSlot τ I) ⟨0⟩

-- `delegateUpdatedProposalCount_accountMapEquiv` / `delegateTrueSuccessMap_accountMapEquiv` were
-- retired when the true-success connect moved to the `EVMStateEquiv` chain
-- (`delegateTrueSuccessState_EVMStateEquiv`); the connect now uses
-- `delegateTrueSuccessState_accountMapEquiv_init` directly on σ_evm.

abbrev delegateWithSenderStore (I : ExecutionEnv) : Store :=
  (delegateStore I).insert "sender" (.storageRef (delegateSenderRef I) voterStructTy)

def delegateVoterRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "voters",
    steps := [.mindex (.address (AccountAddress.ofNat (delegateToWord I).toNat))] }

def delegateVoterFieldRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "voters",
    steps := [.mindex (.address (AccountAddress.ofNat (delegateToWord I).toNat)), .field field] }

abbrev delegateWithDelegateStore (I : ExecutionEnv) : Store :=
  (delegateWithSenderStore I).insert "delegate_" (.storageRef (delegateVoterRef I) voterStructTy)

def delegateSenderPackedCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I)

def delegateSenderVotedByteCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (delegateSenderPackedCurrent evm I) ⟨255⟩

def delegateSenderWeightCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)

def delegateSenderVotedStoreCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (UInt256.land (delegateSenderPackedCurrent evm I) (UInt256.lnot ⟨255⟩)) ⟨1⟩

def delegateAfterVotedState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I)
    (delegateSenderVotedStoreCurrent evm I)

def delegateSenderPackedStoreCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor ⟨1⟩
    (UInt256.lor
      (UInt256.mul (UInt256.land (delegateToWord I) solcAddrMask) ⟨256⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
        (delegateSenderPackedCurrent evm I)))

def delegateAfterSenderState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (delegateAfterVotedState evm I) evm.executionEnv.codeOwner
    (delegateSenderPackedSlot I)
    (delegateSenderPackedStoreCurrent evm I)

@[simp] theorem delegateAfterVotedState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (delegateAfterVotedState evm I).executionEnv = evm.executionEnv := by
  simp [delegateAfterVotedState]

@[simp] theorem delegateAfterSenderState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (delegateAfterSenderState evm I).executionEnv = evm.executionEnv := by
  simp [delegateAfterSenderState]

def delegateVoterWeightCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterSlot (delegateToWord I))

def delegateVoterPackedCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterPackedSlot (delegateToWord I))

def delegateVoterVotedByteCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (delegateVoterPackedCurrent evm I)

def delegateVoterDelegateWordCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (delegateVoterPackedCurrent evm I) ⟨256⟩) solcAddrMask

def delegateVoterVoteCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterVoteSlot (delegateToWord I))

def delegateUpdatedVoterWeightCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (delegateVoterWeightCurrent (delegateAfterSenderState evm I) I)
    (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I)

def delegateFalseSuccessState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (delegateAfterSenderState evm I)
    (delegateAfterSenderState evm I).executionEnv.codeOwner (delegateVoterSlot (delegateToWord I))
    (delegateUpdatedVoterWeightCurrent evm I)

def delegateProposalsLengthCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def delegateProposalCountSlotCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  (⟨1⟩ : UInt256) +
    (UInt256.mul ⟨2⟩ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I) +
      proposalsDataBase)

def delegateProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (delegateAfterSenderState evm I)
    (delegateAfterSenderState evm I).executionEnv.codeOwner (delegateProposalCountSlotCurrent evm I)

def delegateProposalCountEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int
      (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)),
      .field "voteCount"] }

def delegateUpdatedProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (delegateProposalCountCurrent evm I)
    (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I)

def delegateTrueSuccessState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (delegateAfterSenderState evm I)
    (delegateAfterSenderState evm I).executionEnv.codeOwner (delegateProposalCountSlotCurrent evm I)
    (delegateUpdatedProposalCountCurrent evm I)

theorem delegateSourceWord_toNat (I : ExecutionEnv) :
    (delegateSourceWord I).toNat = I.source.val := by
  unfold delegateSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem delegateSourceWord_canonical (I : ExecutionEnv) :
    (delegateSourceWord I).toNat < EVM.addressModulus := by
  rw [delegateSourceWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem delegateSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (delegateSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [delegateSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem delegateWord_eq_of_address_eq_source {I : ExecutionEnv}
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (haddr : AccountAddress.ofNat (delegateToWord I).toNat = I.source) :
    delegateToWord I = delegateSourceWord I := by
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  rw [delegateSourceWord_toNat]
  exact hval

theorem delegateStore_to (I : ExecutionEnv) :
    (delegateStore I).get? "to" = some (delegateToValue I) := by
  simp [delegateStore]

theorem delegateWithSenderStore_to (I : ExecutionEnv) :
    (delegateWithSenderStore I).get? "to" = some (delegateToValue I) := by
  unfold delegateWithSenderStore
  rw [store_get_ne (delegateStore I) (.storageRef (delegateSenderRef I) voterStructTy)
    (by decide), delegateStore_to]

theorem delegateWithDelegateStore_to (I : ExecutionEnv) :
    (delegateWithDelegateStore I).get? "to" = some (delegateToValue I) := by
  unfold delegateWithDelegateStore
  rw [store_get_ne (delegateWithSenderStore I) (.storageRef (delegateVoterRef I) voterStructTy)
    (by decide), delegateWithSenderStore_to]

/-! ### ABI decode -/

theorem ballotDecode_delegate_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (delegateTransition.params.map Param.name)
      (transitionSignature delegateTransition).paramTypes I.calldata = some (delegateStore I) := by
  show decodeCalldata ["to"] [addr] I.calldata = _
  simpa [delegateStore, delegateToValue, delegateToWord, calldataWord, addr]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "to") hsz36 hbig hcanon

theorem ballotDecode_delegate_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (delegateTransition.params.map Param.name)
      (transitionSignature delegateTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short (cd := I.calldata) (x := "to") hsz4 hshort

theorem ballotDecode_delegate_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (delegateToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (delegateTransition.params.map Param.name)
      (transitionSignature delegateTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [delegateToWord, calldataWord, addr] using
    decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "to") hsz36 hbig hnc

theorem ballotDecode_delegate_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (delegateTransition.params.map Param.name)
      (transitionSignature delegateTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "to") hbig

/-! ### Source-level alias facts for the first guard -/

theorem evalStorageRef_delegate_sender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
      evalStorageRef ballotConfig { contract := ballotContract, locals := delegateStore I } evm
      (voterRef sender) = .ok (delegateSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, voterRef, sender,
    evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hsrc]
  rfl

theorem resolveStorageRef_delegate_sender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateStore I } evm
      (voterRef sender) = .ok (delegateSenderRef I, voterStructTy) := by
  exact resolveStorageRef?_ok
    (hbase := by simp [delegateStore, voterRef])
    (her := evalStorageRef_delegate_sender evm I hsrc)
    (hty := by
      simp [delegateSenderRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy])

theorem resolveStorageRef_delegate_senderWeight (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (aliasF "sender" "weight") =
        .ok (delegateSenderFieldRef I "weight", .elem (.int uint256Int)) := by
  simp [resolveStorageRef?, evalStorageRefFrom?, evalStorageRefStep, aliasF,
    delegateWithSenderStore, delegateSenderRef, delegateSenderFieldRef, EvalResult.bind, bind, pure,
    EvalResult.ofOption, storageTypeStep?, voterStructTy, uint256St]

theorem resolveStorageRef_delegate_senderVoted (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (aliasF "sender" "voted") =
        .ok (delegateSenderFieldRef I "voted", .elem .bool) := by
  simp [resolveStorageRef?, evalStorageRefFrom?, evalStorageRefStep, aliasF,
    delegateWithSenderStore, delegateSenderRef, delegateSenderFieldRef, EvalResult.bind, bind, pure,
    EvalResult.ofOption, storageTypeStep?, voterStructTy, boolSt]

theorem evalExpr_delegate_sender_weight (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.storage (aliasF "sender" "weight")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat)) := by
  have hresolve := resolveStorageRef_delegate_senderWeight evm I
  have hread :
      readStorage? ballotConfig evm (delegateSenderFieldRef I "weight") (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateSenderSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_sender_weight_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.storage (aliasF "sender" "weight")) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat)) :=
    evalExpr_delegate_sender_weight evm I
  have hnat : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat ≠
      0 := by
    intro hz
    apply hweight
    apply u256_inj
    exact hz
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hnat]

theorem evalExpr_delegate_sender_weight_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.storage (aliasF "sender" "weight")) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat)) :=
    evalExpr_delegate_sender_weight evm I
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I)).toNat = 0 := by
    rw [hweight]
    rfl
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hnat]

theorem delegateStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem delegateStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool } =
      .bool false := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem delegateStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool } =
      .bool true := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem evalExpr_delegate_sender_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.storage (aliasF "sender" "voted")) = .ok (.bool false) := by
  have hresolve := resolveStorageRef_delegate_senderVoted evm I
  have hread :
      readStorage? ballotConfig evm (delegateSenderFieldRef I "voted") (.elem .bool) =
        .ok (.bool false) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateSenderPackedSlot I, offset := 0, size := 1, hbound := _,
          type := .bool }) =
      EvalResult.ok (Value.bool false)
    rw [delegateStorageLocLoad_bool_offset0_false evm (delegateSenderPackedSlot I)]
    exact hvoted
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_sender_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.storage (aliasF "sender" "voted")) = .ok (.bool true) := by
  have hresolve := resolveStorageRef_delegate_senderVoted evm I
  have hread :
      readStorage? ballotConfig evm (delegateSenderFieldRef I "voted") (.elem .bool) =
        .ok (.bool true) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateSenderPackedSlot I, offset := 0, size := 1, hbound := _,
          type := .bool }) =
      EvalResult.ok (Value.bool true)
    rw [delegateStorageLocLoad_bool_offset0_true evm (delegateSenderPackedSlot I)]
    exact hvoted
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_sender_not_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.unary .not (.storage (aliasF "sender" "voted"))) = .ok (.bool true) := by
  have hstorage := evalExpr_delegate_sender_voted_false evm I hvoted
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem evalExpr_delegate_sender_not_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.unary .not (.storage (aliasF "sender" "voted"))) = .ok (.bool false) := by
  have hstorage := evalExpr_delegate_sender_voted_true evm I hvoted
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem evalExpr_delegate_to_ne_sender_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hself : delegateToWord I = delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.binary .ne (.var "to") sender) = .ok (.bool false) := by
  have haddr : AccountAddress.ofNat (delegateToWord I).toNat = evm.executionEnv.source := by
    simpa [hsrc, hself] using delegateSource_ofNat I
  have htoExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        evm (.var "to") = .ok (delegateToValue I) := by
    rw [evalExpr?]
    exact congrArg (EvalResult.ofOption EvalError.unboundVariable)
      (delegateWithSenderStore_to I)
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        evm sender = .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simp [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateToValue, haddr,
    evalBinaryOp?]

theorem evalExpr_delegate_to_ne_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hnotself : delegateToWord I ≠ delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.binary .ne (.var "to") sender) = .ok (.bool true) := by
  have haddr :
      AccountAddress.ofNat (delegateToWord I).toNat ≠ evm.executionEnv.source := by
    intro h
    apply hnotself
    apply delegateWord_eq_of_address_eq_source hcanon
    simpa [hsrc] using h
  have htoExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        evm (.var "to") = .ok (delegateToValue I) := by
    rw [evalExpr?]
    exact congrArg (EvalResult.ofOption EvalError.unboundVariable)
      (delegateWithSenderStore_to I)
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        evm sender = .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simpa [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateToValue,
    evalBinaryOp?] using haddr

theorem ballotDelegateBodyReverts_weight (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) = ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse
          (evalExpr_delegate_sender_weight_zero_true evm I hweight))

theorem ballotDelegateBodyReverts_voted (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) ≠ ⟨0⟩)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ ≠ ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue
          (evalExpr_delegate_sender_weight_zero_false evm I hweight)) <|
          ExecBlock.consRevert (ExecStmt.requireFalse
            (evalExpr_delegate_sender_not_voted_false evm I hvoted))

theorem ballotDelegateBodyReverts_self (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) ≠ ⟨0⟩)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ = ⟨0⟩)
    (hself : delegateToWord I = delegateSourceWord I) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue
          (evalExpr_delegate_sender_weight_zero_false evm I hweight)) <|
          ExecBlock.consNormal (ExecStmt.requireTrue
            (evalExpr_delegate_sender_not_voted_true evm I hvoted)) <|
            ExecBlock.consRevert (ExecStmt.requireFalse
              (evalExpr_delegate_to_ne_sender_false evm I hsrc hself))

theorem evalExpr_delegate_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.var "to") = .ok (delegateToValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((delegateWithSenderStore I).get? "to") =
    .ok (delegateToValue I)
  rw [delegateWithSenderStore_to]
  rfl

theorem evalExpr_delegate_to_afterDelegate (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.var "to") = .ok (delegateToValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((delegateWithDelegateStore I).get? "to") =
    .ok (delegateToValue I)
  rw [delegateWithDelegateStore_to]
  rfl

theorem evalStorageRef_delegate_voter (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (voterRef (.var "to")) = .ok (delegateVoterRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterRef,
    evalExpr_delegate_to evm I, delegateToValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateVoterRef]

theorem evalStorageRef_delegate_voterField (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (voterF (.var "to") field) = .ok (delegateVoterFieldRef I field) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterF,
    evalExpr_delegate_to evm I, delegateToValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateVoterFieldRef]

theorem resolveStorageRef_delegate_voter (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (voterRef (.var "to")) = .ok (delegateVoterRef I, voterStructTy) := by
  exact resolveStorageRef?_ok
    (hbase := by simp [delegateWithSenderStore, delegateStore, voterRef])
    (her := evalStorageRef_delegate_voter evm I)
    (hty := by
      simp [delegateVoterRef, storageTypeAt?, storageTypeStep?, ballotContract, ballotStorageDecls,
        voterStructTy])

theorem resolveStorageRef_delegate_voterDelegate (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      evm (voterF (.var "to") "delegate") =
        .ok (delegateVoterFieldRef I "delegate", .elem .address) := by
  exact resolveStorageRef?_ok
    (hbase := by simp [delegateWithSenderStore, delegateStore, voterF])
    (her := evalStorageRef_delegate_voterField evm I "delegate")
    (hty := by
      simp [delegateVoterFieldRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy, addrSt])

theorem resolveStorageRef_delegate_delegateField (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      evm (aliasF "delegate_" field) = .ok (delegateVoterFieldRef I field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateWithDelegateStore I).get? "delegate_" =
        some (.storageRef (delegateVoterRef I) voterStructTy) := by
    simp [delegateWithDelegateStore]
  change
    (match (delegateWithDelegateStore I).get? "delegate_" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateWithDelegateStore I } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateWithDelegateStore I } evm
            (aliasF "delegate_" field) with
        | .ok er => do
            let ty' <- EvalResult.ofOption EvalError.storageError
              (storageTypeAt? ballotContract.storage er)
            pure (er, ty')
        | .revert => .revert
        | .error e => .error e) = .ok (delegateVoterFieldRef I field, ty)
  rw [hget]
  simp [evalStorageRefFrom?, evalStorageRefStep, delegateVoterRef, delegateVoterFieldRef,
    EvalResult.bind, EvalResult.ofOption, bind, pure, hty]

theorem resolveStorageRef_delegate_senderField_afterDelegate (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      evm (aliasF "sender" field) = .ok (delegateSenderFieldRef I field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateWithDelegateStore I).get? "sender" =
        some (.storageRef (delegateSenderRef I) voterStructTy) := by
    unfold delegateWithDelegateStore delegateWithSenderStore
    rw [store_get_ne ((delegateStore I).insert "sender"
      (.storageRef (delegateSenderRef I) voterStructTy))
      (.storageRef (delegateVoterRef I) voterStructTy) (by decide)]
    exact store_get_self (delegateStore I) "sender"
      (.storageRef (delegateSenderRef I) voterStructTy)
  change
    (match (delegateWithDelegateStore I).get? "sender" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateWithDelegateStore I } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateWithDelegateStore I } evm
            (aliasF "sender" field) with
        | .ok er => do
            let ty' <- EvalResult.ofOption EvalError.storageError
              (storageTypeAt? ballotContract.storage er)
            pure (er, ty')
        | .revert => .revert
        | .error e => .error e) = .ok (delegateSenderFieldRef I field, ty)
  rw [hget]
  simp [evalStorageRefFrom?, evalStorageRefStep, delegateSenderRef, delegateSenderFieldRef,
    EvalResult.bind, EvalResult.ofOption, bind, pure, hty]

theorem delegateStorageLocLoad_address_offset1 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 1, size := 20, hbound := by decide, type := .address }
      = .address (AccountAddress.ofNat
          (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
            solcAddrMask).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_one]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 1 21))) = _
  rw [List.extract_eq_take_drop, fromBytes'_drop1_take20_wordLE_solcAddrMask]

-- LIBRARY CANDIDATE: `Reasoning.Solm` / packed storage writes.
-- Byte recomposition for the packed `bool,address` slot used by `delegate`.
theorem delegatePackedAddressAfterBoolTrueBytes_toNat (old val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    let w1 := UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩
    fromBytes'
        ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1 ++
          (EVM.Word.toBytesLEWithSizeProof val).1.take 20 ++
          (EVM.Word.toBytesLEWithSizeProof w1).1.drop 21) =
      1 + val.toNat * 2 ^ 8 + (old.toNat / 2 ^ 168) * 2 ^ 168 := by
  intro w1
  have hw1nat : w1.toNat = 1 + 256 * (old.toNat / 256) := by
    simpa [w1] using packedSetTrueWord_toNat old
  have hlow : fromBytes' ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1) = 1 := by
    rw [fromBytes'_take_wordLE_land_mask _ 1 (by decide)]
    rw [u256_land_toNat]
    rw [hw1nat]
    change Nat.land (1 + 256 * (old.toNat / 256)) (2 ^ 8 - 1) % UInt256.size = 1
    rw [nat_land_mask_eq_mod]
    norm_num
    rw [Nat.mod_eq_of_lt (by norm_num [UInt256.size])]
  have hval : fromBytes' ((EVM.Word.toBytesLEWithSizeProof val).1.take 20) = val.toNat := by
    rw [fromBytes'_take20_wordLE_solcAddrMask]
    simpa [u256_land_toNat] using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  have hhigh : fromBytes' ((EVM.Word.toBytesLEWithSizeProof w1).1.drop 21) =
      old.toNat / 2 ^ 168 := by
    rw [fromBytes'_drop_wordLE]
    rw [hw1nat]
    rw [show 256 ^ 21 = 2 ^ 168 by norm_num [Nat.pow_succ, Nat.pow_add]]
    rw [show 2 ^ 168 = 256 * 2 ^ 160 by norm_num [Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [← Nat.div_div_eq_div_mul]
    rw [show (1 + 256 * (old.toNat / 256)) / 256 = old.toNat / 256 by
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)]
      simp]
  rw [fromBytes'_append, fromBytes'_append, hlow, hval, hhigh]
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w1).2]
    norm_num
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
    norm_num
  rw [hlen1, List.length_append, hlen1, hlen20]
  norm_num [Nat.pow_add]
  ring

theorem evalExpr_delegate_voter_delegate (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.storage (voterF (.var "to") "delegate")) =
        .ok (.address (AccountAddress.ofNat (delegateVoterDelegateWordCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_voterDelegate evm I
  have hread :
      readStorage? ballotConfig evm (delegateVoterFieldRef I "delegate") (.elem .address) =
        .ok (.address
          (AccountAddress.ofNat (delegateVoterDelegateWordCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot (delegateToWord I), offset := 1, size := 20,
          hbound := _, type := .address }) =
      EvalResult.ok
        (Value.address (AccountAddress.ofNat (delegateVoterDelegateWordCurrent evm I).toNat))
    rw [delegateStorageLocLoad_address_offset1]
    simp [delegateVoterDelegateWordCurrent, delegateVoterPackedCurrent]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_loop_done (evm : EVM.State) (I : ExecutionEnv)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
      (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr) = .ok (.bool false) := by
  have hstorage := evalExpr_delegate_voter_delegate evm I
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hstorage, zeroAddr,
    evalBinaryOp?, hdelegate, addrSt, castValue?]

theorem delegateAssignVoted (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      evm .storage (aliasF "sender" "voted") (.bool true) =
        .ok ({ contract := ballotContract, locals := delegateWithDelegateStore I },
          delegateAfterVotedState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_senderField_afterDelegate evm I "voted" (.elem .bool)
    (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rw [voteStorageLocStore_bool_true_offset0]
  simp [delegateAfterVotedState, delegateSenderVotedStoreCurrent, delegateSenderPackedCurrent,
    delegateSenderPackedSlot, delegateSenderSlot]

-- LIBRARY CANDIDATE: `Reasoning.Solm` / packed storage writes.
-- Writing the packed `delegate` address after `sender.voted = true` preserves the low bool byte
-- and the high bytes above the address field.
theorem ballotStorageLocStore_address_offset1_after_bool_true (evm : EVM.State)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount evm.executionEnv.codeOwner =
      some acc) (hcanon : val.toNat < EVM.addressModulus)
    {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32} :
    storageLocStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (UInt256.lor
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
              (UInt256.lnot ⟨255⟩)) ⟨1⟩))
        { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address }
        (.address (AccountAddress.ofNat val.toNat)) =
      some (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (UInt256.lor
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
              (UInt256.lnot ⟨255⟩)) ⟨1⟩))
        evm.executionEnv.codeOwner slot
        (UInt256.lor ⟨1⟩
          (UInt256.lor
            (UInt256.mul (UInt256.land val solcAddrMask) ⟨256⟩)
            (UInt256.land
              (UInt256.lnot
                (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))))) := by
  have haddrWord : EVM.Word.ofNat (Fin.toNat (AccountAddress.ofNat val.toNat)) = val := by
    apply u256_inj
    unfold EVM.Word.ofNat UInt256.ofNat AccountAddress.ofNat UInt256.toNat
    change ((val.val.val % AccountAddress.size) % UInt256.size) = val.val.val
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size, UInt256.toNat] using hcanon)]
    exact Nat.mod_eq_of_lt val.val.isLt
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, haddrWord, bind, Option.bind, pure]
  rw [voteStorageStore_executionEnv]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let boolWord := UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩
  have hboolNonzero : (boolWord == default) = false := by
    apply beq_false_of_ne
    intro h
    have hnat := congrArg UInt256.toNat h
    have hw1nat : boolWord.toNat = 1 + 256 * (old.toNat / 256) := by
      simpa [boolWord, old] using packedSetTrueWord_toNat old
    rw [hw1nat] at hnat
    change 1 + 256 * (old.toNat / 256) = 0 at hnat
    omega
  have hload :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot boolWord)
          evm.executionEnv.codeOwner slot = boolWord := by
    exact _root_.Ballot.ballotStorageLoad_storageStore_self_nonzero evm evm.executionEnv.codeOwner slot
      boolWord hacc hboolNonzero
  rw [hload]
  apply congrArg some
  apply congrArg
    (fun w => Solm.EVM.storageStore
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot boolWord)
      evm.executionEnv.codeOwner slot w)
  apply u256_inj
  rw [_root_.Ballot.ballotPackedAddressAfterBoolTrueWord_eq old val hcanon]
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof boolWord).1.take 1 ++
        (EVM.Word.toBytesLEWithSizeProof val).1.take 20 ++
        (EVM.Word.toBytesLEWithSizeProof boolWord).1.drop 21) =
    (UInt256.ofNat (1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168)).toNat
  rw [delegatePackedAddressAfterBoolTrueBytes_toNat old val hcanon]
  have hlt : 1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size := by
    have hq : old.toNat / 2 ^ 168 < 2 ^ 88 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change old.val.val < 2 ^ 256
      simpa [UInt256.size] using old.val.isLt
    have hv : val.toNat < 2 ^ 160 := by
      simpa [EVM.addressModulus, EVM.twoPow] using hcanon
    have hvle : val.toNat ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hv
    have hqle : old.toNat / 2 ^ 168 ≤ 2 ^ 88 - 1 := Nat.le_pred_of_lt hq
    have hvterm : val.toNat * 2 ^ 8 ≤ (2 ^ 160 - 1) * 2 ^ 8 :=
      Nat.mul_le_mul_right _ hvle
    have hqterm :
        old.toNat / 2 ^ 168 * 2 ^ 168 ≤ (2 ^ 88 - 1) * 2 ^ 168 :=
      Nat.mul_le_mul_right _ hqle
    have hmax :
        1 + (2 ^ 160 - 1) * 2 ^ 8 + (2 ^ 88 - 1) * 2 ^ 168 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [ulit_toNat' _ hlt]

theorem delegateAssignDelegate (evm : EVM.State) (I : ExecutionEnv)
    (hacc : evm.lookupAccount evm.executionEnv.codeOwner ≠ none)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterVotedState evm I) .storage (aliasF "sender" "delegate") (delegateToValue I) =
        .ok ({ contract := ballotContract, locals := delegateWithDelegateStore I },
          delegateAfterSenderState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_senderField_afterDelegate (delegateAfterVotedState evm I) I
    "delegate" (.elem .address) (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rcases hlookup : evm.lookupAccount evm.executionEnv.codeOwner with _ | acc
  · exact False.elim (hacc hlookup)
  unfold delegateAfterSenderState delegateAfterVotedState delegateSenderPackedStoreCurrent
    delegateSenderVotedStoreCurrent delegateSenderPackedCurrent delegateToValue
  unfold delegateSenderPackedSlot delegateSenderSlot
  -- Shared packed-slot store helper, supplied from `Common.lean`.
  rw [ballotStorageLocStore_address_offset1_after_bool_true (acc := acc) (hacc := hlookup)
    (hcanon := hcanon)]

theorem evalExpr_delegate_delegate_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : delegateVoterVotedByteCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.storage (aliasF "delegate_" "voted")) = .ok (.bool false) := by
  have hresolve := resolveStorageRef_delegate_delegateField evm I "voted" (.elem .bool) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateVoterFieldRef I "voted") (.elem .bool) =
        .ok (.bool false) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot (delegateToWord I), offset := 0, size := 1,
          hbound := _, type := .bool }) = EvalResult.ok (Value.bool false)
    rw [delegateStorageLocLoad_bool_offset0_false]
    simpa [delegateVoterVotedByteCurrent, delegateVoterPackedCurrent, u256_land_comm] using hzero
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_delegate_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : delegateVoterVotedByteCurrent evm I ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.storage (aliasF "delegate_" "voted")) = .ok (.bool true) := by
  have hresolve := resolveStorageRef_delegate_delegateField evm I "voted" (.elem .bool) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateVoterFieldRef I "voted") (.elem .bool) =
        .ok (.bool true) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot (delegateToWord I), offset := 0, size := 1,
          hbound := _, type := .bool }) = EvalResult.ok (Value.bool true)
    rw [delegateStorageLocLoad_bool_offset0_true]
    simpa [delegateVoterVotedByteCurrent, delegateVoterPackedCurrent, u256_land_comm] using hnz
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_delegate_weight (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.storage (aliasF "delegate_" "weight")) =
        .ok (.int (Int.ofNat (delegateVoterWeightCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_delegateField evm I "weight" (.elem (.int uint256Int))
    (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateVoterFieldRef I "weight")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateVoterWeightCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateVoterWeightCurrent, delegateVoterSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_delegate_weight_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (hweight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) = .ok (.bool true) := by
  have hnat : 1 ≤ (delegateVoterWeightCurrent evm I).toNat := by
    have hnz : (delegateVoterWeightCurrent evm I).toNat ≠ 0 := by
      intro hz
      apply hweight
      apply u256_inj
      exact hz
    omega
  have hstorage := evalExpr_delegate_delegate_weight evm I
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hnat]

theorem evalExpr_delegate_delegate_weight_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hweight : delegateVoterWeightCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_delegate_delegate_weight evm I
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hweight]

theorem evalExpr_delegate_sender_weight_afterDelegate (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.storage (aliasF "sender" "weight")) =
        .ok (.int (Int.ofNat (delegateSenderWeightCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_senderField_afterDelegate evm I "weight"
    (.elem (.int uint256Int)) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateSenderFieldRef I "weight")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateSenderWeightCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateSenderWeightCurrent, delegateSenderSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_delegate_weight_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (delegateVoterWeightCurrent evm I).toNat + (delegateSenderWeightCurrent evm I).toNat <
        UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add (delegateVoterWeightCurrent evm I)
          (delegateSenderWeightCurrent evm I)).toNat)) := by
  have hdel := evalExpr_delegate_delegate_weight evm I
  have hsender := evalExpr_delegate_sender_weight_afterDelegate evm I
  have hlt : ¬ Int.ofNat ((delegateVoterWeightCurrent evm I).toNat +
      (delegateSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat ((delegateVoterWeightCurrent evm I).toNat +
      (delegateSenderWeightCurrent evm I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat (delegateVoterWeightCurrent evm I).toNat +
          Int.ofNat (delegateSenderWeightCurrent evm I).toNat =
        Int.ofNat ((delegateVoterWeightCurrent evm I).toNat +
          (delegateSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  have hword :
      (UInt256.add (delegateVoterWeightCurrent evm I) (delegateSenderWeightCurrent evm I)).toNat =
        (delegateVoterWeightCurrent evm I).toNat + (delegateSenderWeightCurrent evm I).toNat := by
    change ((delegateVoterWeightCurrent evm I) + (delegateSenderWeightCurrent evm I)).toNat = _
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt hfit
  simp [u256, evalExpr?, EvalResult.bind, bind, hdel, hsender, evalBinaryOp?, uint256Int,
    hadd, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact hnonneg hbad
    · exact hlt hbad

theorem evalExpr_delegate_delegate_weight_add_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤
      (delegateVoterWeightCurrent evm I).toNat + (delegateSenderWeightCurrent evm I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hdel := evalExpr_delegate_delegate_weight evm I
  have hsender := evalExpr_delegate_sender_weight_afterDelegate evm I
  have hge : Int.ofNat ((delegateVoterWeightCurrent evm I).toNat +
      (delegateSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hadd :
      Int.ofNat (delegateVoterWeightCurrent evm I).toNat +
          Int.ofNat (delegateSenderWeightCurrent evm I).toNat =
        Int.ofNat ((delegateVoterWeightCurrent evm I).toNat +
          (delegateSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  simp [u256, evalExpr?, EvalResult.bind, bind, hdel, hsender, evalBinaryOp?, uint256Int,
    hadd]
  intro _
  exact_mod_cast hover

theorem delegateAssignVoterWeight (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I) .storage (aliasF "delegate_" "weight")
      (.int (Int.ofNat (delegateUpdatedVoterWeightCurrent evm I).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateWithDelegateStore I },
          delegateFalseSuccessState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_delegateField (delegateAfterSenderState evm I) I "weight"
    (.elem (.int uint256Int)) (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateVoterFieldRef, delegateVoterSlot]
  rw [voteStorageLocStore_uint256]
  simp [delegateFalseSuccessState, delegateUpdatedVoterWeightCurrent, delegateVoterSlot]

theorem evalExpr_delegate_delegate_vote (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I } evm
      (.storage (aliasF "delegate_" "vote")) =
        .ok (.int (Int.ofNat (delegateVoterVoteCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_delegateField evm I "vote" (.elem (.int uint256Int))
    (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateVoterFieldRef I "vote")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateVoterVoteCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateVoterVoteCurrent, delegateVoterVoteSlot, delegateVoterSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem delegateProposalCountSlotCurrent_spec (evm : EVM.State) (I : ExecutionEnv) :
    delegateProposalCountSlotCurrent evm I =
      proposalElemSlot
          (.int (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)) +
        ⟨1⟩ := by
  unfold delegateProposalCountSlotCurrent proposalElemSlot
  rw [keyValueToWord_uint256,
    u256_mul_comm ⟨2⟩ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I),
    u256_mul_two_ofNat]
  rw [u256_add_comm (UInt256.ofNat
    ((delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat * 2)) proposalsDataBase]
  exact u256_add_comm _ _

theorem delegateArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    arrayIndexInBounds? ballotConfig (delegateAfterSenderState evm I) ballotContract.storage
      "proposals" []
      (.int (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)) =
        .ok () := by
  have hboundStorage :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad (delegateAfterSenderState evm I)
          evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [delegateProposalsLengthCurrent] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hboundStorage]

theorem delegateArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    arrayIndexInBounds? ballotConfig (delegateAfterSenderState evm I) ballotContract.storage
      "proposals" []
      (.int (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)) =
        .revert := by
  have hboundStorage :
      ¬ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad (delegateAfterSenderState evm I)
          evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [delegateProposalsLengthCurrent] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad (delegateAfterSenderState evm I)
          evm.executionEnv.codeOwner ⟨2⟩) ≤
        (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hleStorage]

theorem evalStorageRef_delegate_proposalCount (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") =
        .ok (delegateProposalCountEvaledRef evm I) := by
  have hvote := evalExpr_delegate_delegate_vote (delegateAfterSenderState evm I) I
  have hboundsOk :
      arrayIndexInBounds? ballotConfig (delegateAfterSenderState evm I) ballotContract.storage
        "proposals" []
        (.int (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)) =
          .ok () :=
    delegateArrayIndexInBounds_ok evm I hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hvote, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsOk]
  simp [delegateProposalCountEvaledRef]

theorem evalStorageRef_delegate_proposalCount_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") = .revert := by
  have hvote := evalExpr_delegate_delegate_vote (delegateAfterSenderState evm I) I
  have hboundsRevert :
      arrayIndexInBounds? ballotConfig (delegateAfterSenderState evm I) ballotContract.storage
        "proposals" []
        (.int (Int.ofNat (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat)) =
          .revert :=
    delegateArrayIndexInBounds_revert evm I hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hvote, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsRevert]

theorem evalExpr_delegate_proposal_count (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")) =
        .ok (.int (Int.ofNat
          (delegateProposalCountCurrent evm I).toNat)) := by
  have hbase :
      (delegateWithDelegateStore I).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simp [delegateWithDelegateStore, delegateWithSenderStore, delegateStore, proposalF]
  have hty :
      storageTypeAt? ballotContract.storage (delegateProposalCountEvaledRef evm I) =
        some (.elem (.int uint256Int)) := by
    simp [delegateProposalCountEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
      ballotStorageDecls, proposalStructTy, uint256St]
  have hloc :
      ballotConfig.storage.layout (delegateProposalCountEvaledRef evm I) =
        fun _ => some (wordLoc (delegateProposalCountSlotCurrent evm I)) := by
    funext evm'
    simp [delegateProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
      delegateProposalCountSlotCurrent_spec, u256_add_comm]
  have hload :
      storageLocLoad (delegateAfterSenderState evm I)
          (wordLoc (delegateProposalCountSlotCurrent evm I)) =
        .int (Int.ofNat
          (delegateProposalCountCurrent evm I).toNat) := by
    change storageLocLoad (delegateAfterSenderState evm I)
        (wordLoc (delegateProposalCountSlotCurrent evm I)) =
      .int (Int.ofNat (Solm.EVM.storageLoad (delegateAfterSenderState evm I)
        (delegateAfterSenderState evm I).executionEnv.codeOwner
        (delegateProposalCountSlotCurrent evm I)).toNat)
    exact ballotStorageLocLoad_uint256 (delegateAfterSenderState evm I)
      (delegateProposalCountSlotCurrent evm I)
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_delegate_proposalCount evm I hbound) (hty := hty) (hloc := hloc)]
  rw [hload]

theorem evalExpr_delegate_proposal_count_add (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat)
    (hfit :
      (delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add
          (delegateProposalCountCurrent evm I)
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I)).toNat)) := by
  have hcount := evalExpr_delegate_proposal_count evm I hbound
  have hweight := evalExpr_delegate_sender_weight_afterDelegate (delegateAfterSenderState evm I) I
  have hlt : ¬ Int.ofNat
      ((delegateProposalCountCurrent evm I).toNat +
      (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat
      ((delegateProposalCountCurrent evm I).toNat +
      (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat (delegateProposalCountCurrent evm I).toNat +
          Int.ofNat (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat =
        Int.ofNat ((delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) := by
    exact (Int.natCast_add _ _).symm
  have hword :
      (UInt256.add (delegateProposalCountCurrent evm I)
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I)).toNat =
        (delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat := by
    change ((delegateProposalCountCurrent evm I) +
        (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I)).toNat = _
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt hfit
  simp [u256, evalExpr?, EvalResult.bind, bind, hcount, hweight, evalBinaryOp?, uint256Int,
    hadd, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact hnonneg hbad
    · exact hlt hbad

theorem evalExpr_delegate_proposal_count_add_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat)
    (hover : UInt256.size ≤
      (delegateProposalCountCurrent evm I).toNat +
        (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hcount := evalExpr_delegate_proposal_count evm I hbound
  have hweight := evalExpr_delegate_sender_weight_afterDelegate (delegateAfterSenderState evm I) I
  have hge : Int.ofNat
      ((delegateProposalCountCurrent evm I).toNat +
      (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hadd :
      Int.ofNat (delegateProposalCountCurrent evm I).toNat +
          Int.ofNat (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat =
        Int.ofNat ((delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) := by
    exact (Int.natCast_add _ _).symm
  simp [u256, evalExpr?, EvalResult.bind, bind, hcount, hweight, evalBinaryOp?, uint256Int,
    hadd]
  intro _
  exact_mod_cast hover

theorem evalExpr_delegate_proposal_count_add_oob_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hrevert := evalStorageRef_delegate_proposalCount_revert evm I hbound
  have hbase :
      (delegateWithDelegateStore I).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simp [delegateWithDelegateStore, delegateWithSenderStore, delegateStore, proposalF]
  rw [u256, evalExpr?]
  simp only [evalExpr?, hbase, resolveStorageRef?, hrevert, EvalResult.bind, bind]

theorem delegateAssignProposalCount (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat)
    (_hfit :
      (delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.size) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := delegateWithDelegateStore I }
      (delegateAfterSenderState evm I) .storage
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")
      (.int (Int.ofNat (delegateUpdatedProposalCountCurrent evm I).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateWithDelegateStore I },
          delegateTrueSuccessState evm I) := by
  apply assignStorageRef_storage_scalar (er := delegateProposalCountEvaledRef evm I)
      (loc := wordLoc (delegateProposalCountSlotCurrent evm I)) (ty := .elem (.int uint256Int))
      (hbase := by simp [delegateWithDelegateStore, delegateWithSenderStore, delegateStore,
        proposalF])
      (her := evalStorageRef_delegate_proposalCount evm I hbound)
      (hty := by simp [storageTypeAt?, delegateProposalCountEvaledRef, ballotContract,
        ballotStorageDecls, proposalStructTy, uint256St, storageTypeStep?])
      (hloc := by
        funext evm'
        simp [delegateProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
          delegateProposalCountSlotCurrent_spec, u256_add_comm])
  rw [voteStorageLocStore_uint256]
  simp [delegateTrueSuccessState, delegateUpdatedProposalCountCurrent]

theorem delegateSenderWeightCurrent_ne_zero_account (evm : EVM.State) (I : ExecutionEnv)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩) :
    evm.lookupAccount evm.executionEnv.codeOwner ≠ none := by
  intro hnone
  apply hweight
  unfold delegateSenderWeightCurrent Solm.EVM.storageLoad
  rw [hnone]
  rfl

theorem ballotDelegateBodyReverts_delegateWeight (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I = ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_delegate_delegate_weight_ge_false evm I hdelegateWeight))

theorem ballotDelegateBodyReturns_notVoted (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩)
    (hdelegateNotVoted : delegateVoterVotedByteCurrent (delegateAfterSenderState evm I) I = ⟨0⟩)
    (hfit :
      (delegateVoterWeightCurrent (delegateAfterSenderState evm I) I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body
      (.returned { contract := ballotContract, locals := delegateWithDelegateStore I }
        (delegateFalseSuccessState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_delegate_weight_ge_true evm I hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_to_afterDelegate (delegateAfterVotedState evm I) I)
      (delegateAssignDelegate evm I hacc hcanon)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteFalse (evalExpr_delegate_delegate_voted_false
    (delegateAfterSenderState evm I) I hdelegateNotVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_delegate_weight_add (delegateAfterSenderState evm I) I hfit)
      (delegateAssignVoterWeight evm I)) ExecBlock.nil

theorem ballotDelegateBodyReverts_notVotedOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩)
    (hdelegateNotVoted : delegateVoterVotedByteCurrent (delegateAfterSenderState evm I) I = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateVoterWeightCurrent (delegateAfterSenderState evm I) I).toNat +
        (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_delegate_weight_ge_true evm I hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_to_afterDelegate (delegateAfterVotedState evm I) I)
      (delegateAssignDelegate evm I hacc hcanon)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse (evalExpr_delegate_delegate_voted_false
    (delegateAfterSenderState evm I) I hdelegateNotVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_delegate_weight_add_revert (delegateAfterSenderState evm I) I hover))

theorem ballotDelegateBodyReturns_voted (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByteCurrent (delegateAfterSenderState evm I) I ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat)
    (hfit :
      (delegateProposalCountCurrent evm I).toNat +
          (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body
      (.returned { contract := ballotContract, locals := delegateWithDelegateStore I }
        (delegateTrueSuccessState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_delegate_weight_ge_true evm I hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_to_afterDelegate (delegateAfterVotedState evm I) I)
      (delegateAssignDelegate evm I hacc hcanon)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteTrue (evalExpr_delegate_delegate_voted_true
    (delegateAfterSenderState evm I) I hdelegateVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_proposal_count_add evm I hbound hfit)
      (delegateAssignProposalCount evm I hbound hfit)) ExecBlock.nil

theorem ballotDelegateBodyReverts_votedOob (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByteCurrent (delegateAfterSenderState evm I) I ≠ ⟨0⟩)
    (hbound :
      ¬ (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_delegate_weight_ge_true evm I hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_to_afterDelegate (delegateAfterVotedState evm I) I)
      (delegateAssignDelegate evm I hacc hcanon)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue (evalExpr_delegate_delegate_voted_true
    (delegateAfterSenderState evm I) I hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_proposal_count_add_oob_revert evm I hbound))

theorem ballotDelegateBodyReverts_votedOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWordCurrent evm I = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightCurrent evm I ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByteCurrent (delegateAfterSenderState evm I) I ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteCurrent (delegateAfterSenderState evm I) I).toNat <
        (delegateProposalsLengthCurrent (delegateAfterSenderState evm I)).toNat)
    (hover : UInt256.size ≤
      (delegateProposalCountCurrent evm I).toNat +
        (delegateSenderWeightCurrent (delegateAfterSenderState evm I) I).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.whileFalse (evalExpr_delegate_loop_done evm I hdelegate)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_voter evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_delegate_weight_ge_true evm I hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_to_afterDelegate (delegateAfterVotedState evm I) I)
      (delegateAssignDelegate evm I hacc hcanon)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue (evalExpr_delegate_delegate_voted_true
    (delegateAfterSenderState evm I) I hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_proposal_count_add_revert evm I hbound hover))

theorem delegateSenderWeightCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateSenderWeightCurrent (initState cA gh bl σ σ₀ g A I) I =
      delegateSenderWeightWord σ I := by
  rfl

theorem delegateSenderVotedByteCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateSenderVotedByteCurrent (initState cA gh bl σ σ₀ g A I) I =
      delegateSenderVotedByte σ I := by
  unfold delegateSenderVotedByteCurrent delegateSenderVotedByte delegateSenderPackedCurrent
    delegateSenderPackedWord
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, initState,
    u256_land_comm]

theorem delegateVoterWeightCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateVoterWeightCurrent (initState cA gh bl σ σ₀ g A I) I =
      delegateVoterWeightWord σ I (delegateToWord I) := by
  rfl

theorem delegateVoterDelegateWordCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateVoterDelegateWordCurrent (initState cA gh bl σ σ₀ g A I) I =
      delegateVoterDelegateWord σ I (delegateToWord I) := by
  rfl

theorem u256_lor_one_ne_zero (w : UInt256) : UInt256.lor ⟨1⟩ w ≠ ⟨0⟩ := by
  intro h
  have hval : (UInt256.lor ⟨1⟩ w).toNat = 0 := by
    simpa using congrArg UInt256.toNat h
  rw [u256_lor_toNat] at hval
  change Nat.lor 1 w.toNat % UInt256.size = 0 at hval
  have hlt : Nat.lor 1 w.toNat < UInt256.size := by
    have hw : w.toNat < 2 ^ 256 := by
      simpa [UInt256.toNat, UInt256.size] using w.val.isLt
    simpa [UInt256.size] using Nat.or_lt_two_pow (by norm_num : 1 < 2 ^ 256) hw
  rw [Nat.mod_eq_of_lt hlt] at hval
  have hbitTrue : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
    change Nat.testBit (1 ||| w.toNat) 0 = true
    rw [Nat.testBit_lor]
    norm_num
  rw [hval] at hbitTrue
  simp at hbitTrue

theorem delegateSenderPackedStoreWord_ne_zero (σ : AccountMap) (I : ExecutionEnv) :
    delegateSenderPackedStoreWord σ I ≠ ⟨0⟩ := by
  unfold delegateSenderPackedStoreWord
  exact u256_lor_one_ne_zero _

theorem delegateAfterSenderState_findD_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (readSlot : UInt256) :
    (((delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I).accountMap.find?
          (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner).option
        (default : UInt256)
        (fun acc => acc.storage.findD readSlot default)) =
      (((delegateAfterSenderMap σ I).find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot default)) := by
  have hfinal : (delegateSenderPackedStoreWord σ I == (default : UInt256)) = false := by
    simpa using delegateSenderPackedStoreWord_ne_zero σ I
  have hlookup := sstoreAccountMap_self_storage_findD_update_insert_self
    σ I.codeOwner (delegateSenderPackedSlot I) readSlot
    (delegateSenderVotedStoreCurrent (initState cA gh bl σ σ₀ g A I) I)
    (delegateSenderPackedStoreWord σ I) hfinal
  simpa [delegateAfterSenderState, delegateAfterVotedState, delegateAfterSenderMap,
    delegateSenderPackedStoreCurrent, delegateSenderPackedStoreWord, delegateSenderVotedStoreCurrent,
    delegateSenderPackedCurrent, delegateSenderPackedWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, storageStore_accountMap, voteStorageStore_executionEnv]
    using hlookup

theorem delegateVoterVotedByteCurrent_afterSenderState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateVoterVotedByteCurrent
        (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I) I =
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) := by
  simpa [delegateVoterVotedByteCurrent, delegateVoterVotedByte, delegateVoterPackedCurrent,
    delegateVoterPackedWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    using congrArg (fun w => UInt256.land ⟨255⟩ w)
      (delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (delegateVoterPackedSlot (delegateToWord I)))

theorem delegateVoterWeightCurrent_afterSenderState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateVoterWeightCurrent
        (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I) I =
      delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I) := by
  simpa [delegateVoterWeightCurrent, delegateVoterWeightWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (delegateVoterSlot (delegateToWord I))

theorem delegateSenderWeightCurrent_afterSenderState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateSenderWeightCurrent
        (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I) I =
      delegateSenderWeightWord (delegateAfterSenderMap σ I) I := by
  simpa [delegateSenderWeightCurrent, delegateSenderWeightWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (delegateSenderSlot I)

theorem delegateVoterVoteCurrent_afterSenderState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateVoterVoteCurrent
        (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I) I =
      delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I) := by
  simpa [delegateVoterVoteCurrent, delegateVoterVoteWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (delegateVoterVoteSlot (delegateToWord I))

theorem delegateProposalsLengthCurrent_afterSenderState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateProposalsLengthCurrent
        (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I) =
      delegateProposalsLengthWord σ I := by
  simpa [delegateProposalsLengthCurrent, delegateProposalsLengthWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) ⟨2⟩

theorem delegateProposalCountCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    delegateProposalCountCurrent (initState cA gh bl σ σ₀ g A I) I =
      delegateProposalCountWord σ I := by
  unfold delegateProposalCountCurrent delegateProposalCountSlotCurrent
  rw [delegateVoterVoteCurrent_afterSenderState_init]
  simpa [delegateProposalCountWord, delegateProposalCountSlot, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, initState, voteStorageStore_executionEnv]
    using delegateAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (delegateProposalCountSlot σ I)

theorem u256_add_ne_zero_of_right_ne_zero {a b : UInt256}
    (hb : b ≠ ⟨0⟩) (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.add a b ≠ ⟨0⟩ := by
  intro hzero
  have hnat : (UInt256.add a b).toNat = a.toNat + b.toNat := by
    change (a + b).toNat = _
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt hfit
  have hsum : a.toNat + b.toNat = 0 := by
    have hz := congrArg UInt256.toNat hzero
    simpa [hnat] using hz
  have hbNat : b.toNat = 0 := by omega
  exact hb (uint256_toNat_eq_zero hbNat)

theorem u256_add_one_ne_self (a : UInt256) : a + ⟨1⟩ ≠ a := by
  intro h
  have hmod : (a.toNat + 1) % UInt256.size = a.toNat := by
    have hnat := congrArg UInt256.toNat h
    simpa [uadd_toNat] using hnat
  have ha : a.toNat < UInt256.size := a.val.isLt
  by_cases hlt : a.toNat + 1 < UInt256.size
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have hge : UInt256.size ≤ a.toNat + 1 := Nat.le_of_not_gt hlt
    have hle : a.toNat + 1 ≤ UInt256.size := Nat.succ_le_of_lt ha
    have heq : a.toNat + 1 = UInt256.size := le_antisymm hle hge
    rw [heq, Nat.mod_self] at hmod
    have hsize : 1 < UInt256.size := by norm_num [UInt256.size]
    omega

theorem delegateSenderSlot_ne_packedSlot (I : ExecutionEnv) :
    delegateSenderSlot I ≠ delegateSenderPackedSlot I := by
  intro h
  exact (u256_add_one_ne_self (delegateSenderSlot I))
    (by simpa [delegateSenderPackedSlot] using h.symm)

theorem delegateSenderWeightWord_afterSenderMap (σ : AccountMap) (I : ExecutionEnv) :
    delegateSenderWeightWord (delegateAfterSenderMap σ I) I =
      delegateSenderWeightWord σ I := by
  unfold delegateSenderWeightWord delegateAfterSenderMap
  exact sstoreAccountMap_storage_findD_ne σ I.codeOwner (delegateSenderSlot I)
    (delegateSenderPackedSlot I) (delegateSenderPackedStoreWord σ I)
    (delegateSenderSlot_ne_packedSlot I)

theorem delegateUpdatedVoterWeight_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size) :
    delegateUpdatedVoterWeight σ I ≠ ⟨0⟩ := by
  unfold delegateUpdatedVoterWeight
  apply u256_add_ne_zero_of_right_ne_zero
  · simpa [delegateSenderWeightWord_afterSenderMap] using hweight
  · exact hfit

theorem delegateUpdatedProposalCount_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateProposalCountWord σ I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size) :
    delegateUpdatedProposalCount σ I ≠ ⟨0⟩ := by
  unfold delegateUpdatedProposalCount
  apply u256_add_ne_zero_of_right_ne_zero
  · simpa [delegateSenderWeightWord_afterSenderMap] using hweight
  · exact hfit

theorem delegateAfterSenderState_accountMapEquiv_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (delegateAfterSenderMap σ I)
      (delegateAfterSenderState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  have hfinal : (delegateSenderPackedStoreWord σ I == (default : UInt256)) = false := by
    simpa using delegateSenderPackedStoreWord_ne_zero σ I
  have h := accountMapEquiv_sstoreAccountMap_self_update_insert
    σ I.codeOwner (delegateSenderPackedSlot I)
    (delegateSenderVotedStoreCurrent (initState cA gh bl σ σ₀ g A I) I)
    (delegateSenderPackedStoreWord σ I) hfinal
  simpa [delegateAfterSenderState, delegateAfterVotedState, delegateAfterSenderMap,
    delegateSenderPackedStoreCurrent, delegateSenderPackedStoreWord, delegateSenderVotedStoreCurrent,
    delegateSenderPackedCurrent, delegateSenderPackedWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, storageStore_accountMap, voteStorageStore_executionEnv]
    using h

theorem delegateFalseSuccessState_created_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    cA = (delegateFalseSuccessState (initState cA gh bl σ σ₀ g A I) I).createdAccounts := by
  simp [delegateFalseSuccessState, delegateAfterSenderState, delegateAfterVotedState,
    initState, storageStore_createdAccounts]

theorem delegateFalseSuccessState_accountMapEquiv_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size) :
    accountMapEquiv (delegateFalseSuccessMap σ I)
      (delegateFalseSuccessState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  have hfinal : (delegateUpdatedVoterWeight σ I == (default : UInt256)) = false := by
    simpa using delegateUpdatedVoterWeight_ne_zero σ I hweight hfit
  have hbase := delegateAfterSenderState_accountMapEquiv_init
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have h := accountMapEquiv_sstoreAccountMap_insert I.codeOwner
    (delegateVoterSlot (delegateToWord I)) (delegateUpdatedVoterWeight σ I) hbase hfinal
  simpa [delegateFalseSuccessState, delegateFalseSuccessMap, delegateUpdatedVoterWeightCurrent,
    delegateUpdatedVoterWeight, delegateVoterWeightCurrent_afterSenderState_init,
    delegateSenderWeightCurrent_afterSenderState_init, storageStore_accountMap,
    voteStorageStore_executionEnv] using h

theorem delegateTrueSuccessState_created_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    cA = (delegateTrueSuccessState (initState cA gh bl σ σ₀ g A I) I).createdAccounts := by
  simp [delegateTrueSuccessState, delegateAfterSenderState, delegateAfterVotedState,
    initState, storageStore_createdAccounts]

theorem delegateTrueSuccessState_accountMapEquiv_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateProposalCountWord σ I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size) :
    accountMapEquiv (delegateTrueSuccessMap σ I)
      (delegateTrueSuccessState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  have hfinal : (delegateUpdatedProposalCount σ I == (default : UInt256)) = false := by
    simpa using delegateUpdatedProposalCount_ne_zero σ I hweight hfit
  have hbase := delegateAfterSenderState_accountMapEquiv_init
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have h := accountMapEquiv_sstoreAccountMap_insert I.codeOwner
    (delegateProposalCountSlot σ I) (delegateUpdatedProposalCount σ I) hbase hfinal
  simpa [delegateTrueSuccessState, delegateTrueSuccessMap, delegateUpdatedProposalCountCurrent,
    delegateUpdatedProposalCount, delegateProposalCountCurrent_init,
    delegateSenderWeightCurrent_afterSenderState_init, delegateProposalCountSlot,
    delegateProposalCountSlotCurrent, delegateVoterVoteCurrent_afterSenderState_init,
    storageStore_accountMap, voteStorageStore_executionEnv] using h

/-! ### `EVMStateEquiv` simulation chains for the delegate success states

These carry the simulation relation compositionally through the writes, with the value/slot
agreements for σ-dependent writes coming from the chain's own `storageLoad` agreement.  They are
the delegate analogue of `voteFinalState_EVMStateEquiv` and feed the relaxed
`reEquivExecutionGenEVMStateEquiv` connect (its `acc.2` side is up to `accountMapEquiv`, which
absorbs the packed same-slot double write in `delegateAfterSenderState`). -/

theorem delegateAfterSenderState_EVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (delegateAfterSenderState (initState cA gh bl σ_evm σ₀ g A I) I)
      (delegateAfterSenderState (initState cA gh bl σ_solm σ₀ g A I) I) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := EVMStateEquiv.initState hAccounts
  have hVoted : delegateSenderVotedStoreCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      delegateSenderVotedStoreCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold delegateSenderVotedStoreCurrent delegateSenderPackedCurrent
    rw [hσ.storageLoad_codeOwner (delegateSenderPackedSlot I)]
  have hσVoted : EVMStateEquiv (delegateAfterVotedState (initState cA gh bl σ_evm σ₀ g A I) I)
      (delegateAfterVotedState (initState cA gh bl σ_solm σ₀ g A I) I) := by
    unfold delegateAfterVotedState
    exact hσ.storageStore_codeOwner (delegateSenderPackedSlot I) hVoted
  have hSender : delegateSenderPackedStoreCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      delegateSenderPackedStoreCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold delegateSenderPackedStoreCurrent delegateSenderPackedCurrent
    rw [hσ.storageLoad_codeOwner (delegateSenderPackedSlot I)]
  unfold delegateAfterSenderState
  exact hσVoted.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
    (delegateSenderPackedSlot I) hSender

theorem delegateFalseSuccessState_EVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (delegateFalseSuccessState (initState cA gh bl σ_evm σ₀ g A I) I)
      (delegateFalseSuccessState (initState cA gh bl σ_solm σ₀ g A I) I) := by
  have hσS := delegateAfterSenderState_EVMStateEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hAccounts
  have hW : delegateUpdatedVoterWeightCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      delegateUpdatedVoterWeightCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold delegateUpdatedVoterWeightCurrent delegateVoterWeightCurrent delegateSenderWeightCurrent
    rw [hσS.storageLoad_codeOwner (delegateVoterSlot (delegateToWord I)),
      hσS.storageLoad_codeOwner (delegateSenderSlot I)]
  unfold delegateFalseSuccessState
  exact hσS.storageStore_codeOwner (delegateVoterSlot (delegateToWord I)) hW

theorem delegateTrueSuccessState_EVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (delegateTrueSuccessState (initState cA gh bl σ_evm σ₀ g A I) I)
      (delegateTrueSuccessState (initState cA gh bl σ_solm σ₀ g A I) I) := by
  have hσS := delegateAfterSenderState_EVMStateEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hAccounts
  have hSlot : delegateProposalCountSlotCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      delegateProposalCountSlotCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold delegateProposalCountSlotCurrent delegateVoterVoteCurrent
    rw [hσS.storageLoad_codeOwner (delegateVoterVoteSlot (delegateToWord I))]
  have hCount : delegateUpdatedProposalCountCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      delegateUpdatedProposalCountCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold delegateUpdatedProposalCountCurrent delegateProposalCountCurrent delegateSenderWeightCurrent
    rw [hSlot, hσS.storageLoad_codeOwner (delegateProposalCountSlotCurrent
        (initState cA gh bl σ_solm σ₀ g A I) I),
      hσS.storageLoad_codeOwner (delegateSenderSlot I)]
  unfold delegateTrueSuccessState
  rw [hSlot]
  exact hσS.storageStore_codeOwner
    (delegateProposalCountSlotCurrent (initState cA gh bl σ_solm σ₀ g A I) I) hCount

/-! ### Memory helpers for the sender mapping slot -/

noncomputable def delegateKeyMem (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray senderWord).write 0 solcFreePtrMem 0 32

noncomputable def delegateHashMem (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (delegateKeyMem senderWord) 32 32

noncomputable def delegateLoopKeyMem (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray toWord).write 0 (delegateHashMem senderWord) 0 32

noncomputable def delegateLoopHashMem (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (delegateLoopKeyMem toWord senderWord) 32 32

noncomputable def delegateProposalBaseMem (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0
    (delegateLoopHashMem toWord senderWord) 0 32

theorem delegateKeyMem_size (senderWord : UInt256) : (delegateKeyMem senderWord).size = 96 := by
  unfold delegateKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem delegateHashMem_size (senderWord : UInt256) : (delegateHashMem senderWord).size = 96 := by
  unfold delegateHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [delegateKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateKeyMem_size, toByteArray_size]
  omega

theorem delegateLoopKeyMem_size (toWord senderWord : UInt256) :
    (delegateLoopKeyMem toWord senderWord).size = 96 := by
  unfold delegateLoopKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [delegateHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateHashMem_size, toByteArray_size]
  omega

theorem delegateLoopHashMem_size (toWord senderWord : UInt256) :
    (delegateLoopHashMem toWord senderWord).size = 96 := by
  unfold delegateLoopHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [delegateLoopKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateLoopKeyMem_size, toByteArray_size]
  omega

theorem delegateKeyMem_read0 (senderWord : UInt256) :
    (delegateKeyMem senderWord).readWithPadding 0 32 = UInt256.toByteArray senderWord := by
  unfold delegateKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray senderWord).extract 0 32 = UInt256.toByteArray senderWord from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray senderWord).size ≤ 32
        rw [toByteArray_size])]

theorem delegateKeyMem_read64 (senderWord : UInt256) :
    (delegateKeyMem senderWord).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold delegateKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem delegateHashMem_read0 (senderWord : UInt256) :
    (delegateHashMem senderWord).readWithPadding 0 32 = UInt256.toByteArray senderWord := by
  unfold delegateHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [delegateKeyMem_size]; omega) (by omega),
    delegateKeyMem_read0]

theorem delegateHashMem_read32 (senderWord : UInt256) :
    (delegateHashMem senderWord).readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold delegateHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [delegateKeyMem_size]; omega),
    show (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem delegateHashMem_read64 (senderWord : UInt256) :
    (delegateHashMem senderWord).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold delegateHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [delegateKeyMem_size]; omega) (by omega)
      (by rw [delegateKeyMem_size]),
    delegateKeyMem_read64]

theorem delegateLoopKeyMem_read0 (toWord senderWord : UInt256) :
    (delegateLoopKeyMem toWord senderWord).readWithPadding 0 32 =
      UInt256.toByteArray toWord := by
  unfold delegateLoopKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [delegateHashMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray toWord).size ≤ 32
    rw [toByteArray_size])

theorem delegateLoopKeyMem_read64 (toWord senderWord : UInt256) :
    (delegateLoopKeyMem toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [delegateHashMem_size]; omega) (by omega)
      (by rw [delegateHashMem_size]),
    delegateHashMem_read64]

theorem delegateLoopHashMem_read0 (toWord senderWord : UInt256) :
    (delegateLoopHashMem toWord senderWord).readWithPadding 0 32 =
      UInt256.toByteArray toWord := by
  unfold delegateLoopHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega) (by omega),
    delegateLoopKeyMem_read0]

theorem delegateLoopHashMem_read32 (toWord senderWord : UInt256) :
    (delegateLoopHashMem toWord senderWord).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold delegateLoopHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem delegateLoopHashMem_read64 (toWord senderWord : UInt256) :
    (delegateLoopHashMem toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega) (by omega)
      (by rw [delegateLoopKeyMem_size]),
    delegateLoopKeyMem_read64]

theorem delegateProposalBaseMem_read0 (toWord senderWord : UInt256) :
    (delegateProposalBaseMem toWord senderWord).readWithPadding 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold delegateProposalBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [delegateLoopHashMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨2⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem delegateHashMem_mload64 (senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateHashMem senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateHashMem senderWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateHashMem_size]; decide) (by decide)
    (delegateHashMem_read64 senderWord)

theorem delegateLoopHashMem_mload64 (toWord senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateLoopHashMem toWord senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateLoopHashMem toWord senderWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateLoopHashMem_size]; decide) (by decide)
    (delegateLoopHashMem_read64 toWord senderWord)

def delegateErrorSelector : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

def delegateWeightStringWord : UInt256 :=
  ⟨40452771926134549143109899274521035002332574754166580779127900301869740720128⟩

noncomputable def delegateWeightErrorMem0 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateErrorSelector).write 0 (delegateHashMem senderWord) 128 32

noncomputable def delegateWeightErrorMem1 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (delegateWeightErrorMem0 senderWord) 132 32

noncomputable def delegateWeightErrorMem2 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0 (delegateWeightErrorMem1 senderWord) 164 32

noncomputable def delegateWeightErrorMem3 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateWeightStringWord).write 0
    (delegateWeightErrorMem2 senderWord) 196 32

theorem delegateWeightErrorMem0_size (senderWord : UInt256) :
    (delegateWeightErrorMem0 senderWord).size = 160 := by
  unfold delegateWeightErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [delegateHashMem_size]; omega)
      (by rw [delegateHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, delegateHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem delegateWeightErrorMem1_size (senderWord : UInt256) :
    (delegateWeightErrorMem1 senderWord).size = 164 := by
  unfold delegateWeightErrorMem1
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem0_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateWeightErrorMem0_size,
    toByteArray_size]
  omega

theorem delegateWeightErrorMem2_size (senderWord : UInt256) :
    (delegateWeightErrorMem2 senderWord).size = 196 := by
  unfold delegateWeightErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateWeightErrorMem1_size,
    toByteArray_size]
  omega

theorem delegateWeightErrorMem3_size (senderWord : UInt256) :
    (delegateWeightErrorMem3 senderWord).size = 228 := by
  unfold delegateWeightErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateWeightErrorMem2_size,
    toByteArray_size]
  omega

theorem delegateWeightErrorMem0_read64 (senderWord : UInt256) :
    (delegateWeightErrorMem0 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateWeightErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [delegateHashMem_size]; omega)
      (by rw [delegateHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, delegateHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, delegateHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [delegateHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [delegateHashMem_size])]
  exact delegateHashMem_read64 senderWord

theorem delegateWeightErrorMem1_read64 (senderWord : UInt256) :
    (delegateWeightErrorMem1 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateWeightErrorMem1
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem0_size]; omega) (by omega),
    delegateWeightErrorMem0_read64]

theorem delegateWeightErrorMem2_read64 (senderWord : UInt256) :
    (delegateWeightErrorMem2 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateWeightErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]) (by omega),
    delegateWeightErrorMem1_read64]

theorem delegateWeightErrorMem3_read64 (senderWord : UInt256) :
    (delegateWeightErrorMem3 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateWeightErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem2_size]) (by omega),
    delegateWeightErrorMem2_read64]

theorem delegateWeightErrorMem3_mload64 (senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateWeightErrorMem3 senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateWeightErrorMem3 senderWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateWeightErrorMem3_size]; decide) (by decide)
    (delegateWeightErrorMem3_read64 senderWord)

def delegateVotedStringRaw : UInt256 :=
  ⟨0x2cb7ba9030b63932b0b23c903b37ba32b217⟩

def delegateVotedStringWord : UInt256 :=
  UInt256.shiftLeft delegateVotedStringRaw ⟨113⟩

noncomputable def delegateVotedErrorMem2 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨18⟩ : UInt256)).write 0 (delegateWeightErrorMem1 senderWord) 164 32

noncomputable def delegateVotedErrorMem3 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateVotedStringWord).write 0
    (delegateVotedErrorMem2 senderWord) 196 32

theorem delegateVotedErrorMem2_size (senderWord : UInt256) :
    (delegateVotedErrorMem2 senderWord).size = 196 := by
  unfold delegateVotedErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateWeightErrorMem1_size,
    toByteArray_size]
  omega

theorem delegateVotedErrorMem3_size (senderWord : UInt256) :
    (delegateVotedErrorMem3 senderWord).size = 228 := by
  unfold delegateVotedErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [delegateVotedErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateVotedErrorMem2_size,
    toByteArray_size]
  omega

theorem delegateVotedErrorMem2_read64 (senderWord : UInt256) :
    (delegateVotedErrorMem2 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateVotedErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]) (by omega),
    delegateWeightErrorMem1_read64]

theorem delegateVotedErrorMem3_read64 (senderWord : UInt256) :
    (delegateVotedErrorMem3 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateVotedErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [delegateVotedErrorMem2_size]) (by omega),
    delegateVotedErrorMem2_read64]

theorem delegateVotedErrorMem3_mload64 (senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateVotedErrorMem3 senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateVotedErrorMem3 senderWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateVotedErrorMem3_size]; decide) (by decide)
    (delegateVotedErrorMem3_read64 senderWord)

def delegateSelfStringWord : UInt256 :=
  ⟨0x53656c662d64656c65676174696f6e20697320646973616c6c6f7765642e0000⟩

noncomputable def delegateSelfErrorMem2 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨30⟩ : UInt256)).write 0 (delegateWeightErrorMem1 senderWord) 164 32

noncomputable def delegateSelfErrorMem3 (senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateSelfStringWord).write 0
    (delegateSelfErrorMem2 senderWord) 196 32

theorem delegateSelfErrorMem2_size (senderWord : UInt256) :
    (delegateSelfErrorMem2 senderWord).size = 196 := by
  unfold delegateSelfErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateWeightErrorMem1_size,
    toByteArray_size]
  omega

theorem delegateSelfErrorMem3_size (senderWord : UInt256) :
    (delegateSelfErrorMem3 senderWord).size = 228 := by
  unfold delegateSelfErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [delegateSelfErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateSelfErrorMem2_size,
    toByteArray_size]
  omega

theorem delegateSelfErrorMem2_read64 (senderWord : UInt256) :
    (delegateSelfErrorMem2 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateSelfErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [delegateWeightErrorMem1_size]) (by omega),
    delegateWeightErrorMem1_read64]

theorem delegateSelfErrorMem3_read64 (senderWord : UInt256) :
    (delegateSelfErrorMem3 senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateSelfErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [delegateSelfErrorMem2_size]) (by omega),
    delegateSelfErrorMem2_read64]

theorem delegateSelfErrorMem3_mload64 (senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateSelfErrorMem3 senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateSelfErrorMem3 senderWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateSelfErrorMem3_size]; decide) (by decide)
    (delegateSelfErrorMem3_read64 senderWord)

theorem delegateHashMem_read0_64 (senderWord : UInt256) :
    (delegateHashMem senderWord).readWithPadding 0 64 =
      UInt256.toByteArray senderWord ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [delegateHashMem_size]; omega)]
  unfold delegateHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [delegateKeyMem_size]; omega)]
  have hsenderFull :
      (UInt256.toByteArray senderWord).extract 0 32 = UInt256.toByteArray senderWord := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray senderWord).size ≤ 32
      rw [toByteArray_size])
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hkey0 :
      (delegateKeyMem senderWord).extract 0 32 = UInt256.toByteArray senderWord := by
    have hread := delegateKeyMem_read0 senderWord
    rw [readWithPadding_eq_extract _ 0 (by rw [delegateKeyMem_size]; omega)] at hread
    exact hread
  rw [hbaseFull]
  rw [ByteArray.append_assoc]
  rw [extract_append_span ((delegateKeyMem senderWord).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateKeyMem senderWord).extract (32 + 32) (delegateKeyMem senderWord).size) 0 64
      (by omega) (by rw [ByteArray.size_extract, delegateKeyMem_size]; omega)]
  rw [show ((delegateKeyMem senderWord).extract 0 32).size = 32 from by
      rw [ByteArray.size_extract, delegateKeyMem_size]; omega]
  rw [show 64 - 32 = 32 from rfl]
  rw [hkey0, hsenderFull]
  rw [extract_append_left _ _ 0 32 (by rw [toByteArray_size])]
  rw [hbaseFull]

theorem delegateLoopHashMem_read0_64 (toWord senderWord : UInt256) :
    (delegateLoopHashMem toWord senderWord).readWithPadding 0 64 =
      UInt256.toByteArray toWord ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [delegateLoopHashMem_size]; omega)]
  unfold delegateLoopHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega)]
  have htoFull :
      (UInt256.toByteArray toWord).extract 0 32 = UInt256.toByteArray toWord := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray toWord).size ≤ 32
      rw [toByteArray_size])
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hkey0 :
      (delegateLoopKeyMem toWord senderWord).extract 0 32 = UInt256.toByteArray toWord := by
    have hread := delegateLoopKeyMem_read0 toWord senderWord
    rw [readWithPadding_eq_extract _ 0 (by rw [delegateLoopKeyMem_size]; omega)] at hread
    exact hread
  rw [hbaseFull]
  rw [ByteArray.append_assoc]
  rw [extract_append_span ((delegateLoopKeyMem toWord senderWord).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateLoopKeyMem toWord senderWord).extract (32 + 32)
          (delegateLoopKeyMem toWord senderWord).size) 0 64
      (by omega) (by rw [ByteArray.size_extract, delegateLoopKeyMem_size]; omega)]
  rw [show ((delegateLoopKeyMem toWord senderWord).extract 0 32).size = 32 from by
      rw [ByteArray.size_extract, delegateLoopKeyMem_size]; omega]
  rw [show 64 - 32 = 32 from rfl]
  rw [hkey0, htoFull]
  rw [extract_append_left _ _ 0 32 (by rw [toByteArray_size])]
  rw [hbaseFull]

theorem delegateLoopHashMem_writeKey (toWord senderWord : UInt256) :
    (UInt256.toByteArray toWord).write 0 (delegateLoopHashMem toWord senderWord) 0 32 =
      delegateLoopHashMem toWord senderWord := by
  rw [write32_eq _ _ 0 (by rw [toByteArray_size])
      (by rw [delegateLoopHashMem_size]; omega)]
  have hempty : (delegateLoopHashMem toWord senderWord).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have htoFull : (UInt256.toByteArray toWord).extract 0 32 = UInt256.toByteArray toWord := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray toWord).size ≤ 32
      rw [toByteArray_size])
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have htail :
      (delegateLoopHashMem toWord senderWord).extract 32
          (delegateLoopHashMem toWord senderWord).size =
        UInt256.toByteArray (⟨1⟩ : UInt256) ++
          (delegateLoopKeyMem toWord senderWord).extract 64
            (delegateLoopKeyMem toWord senderWord).size := by
    unfold delegateLoopHashMem
    rw [write32_eq _ _ 32 (by rw [toByteArray_size])
        (by rw [delegateLoopKeyMem_size]; omega)]
    rw [hbaseFull]
    rw [ByteArray.append_assoc]
    rw [extract_append_right_window ((delegateLoopKeyMem toWord senderWord).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateLoopKeyMem toWord senderWord).extract (32 + 32)
          (delegateLoopKeyMem toWord senderWord).size) 32
      (((delegateLoopKeyMem toWord senderWord).extract 0 32) ++
        (UInt256.toByteArray (⟨1⟩ : UInt256) ++
          (delegateLoopKeyMem toWord senderWord).extract (32 + 32)
            (delegateLoopKeyMem toWord senderWord).size)).size
      (by rw [ByteArray.size_extract, delegateLoopKeyMem_size]; omega)]
    rw [show 32 + 32 = 64 from rfl]
    have hprefixSize : ((delegateLoopKeyMem toWord senderWord).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, delegateLoopKeyMem_size]
      omega
    simpa [hprefixSize, ByteArray.size_append] using byteArray_extract_self
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateLoopKeyMem toWord senderWord).extract 64
          (delegateLoopKeyMem toWord senderWord).size)
  have hkey0 :
      (delegateLoopKeyMem toWord senderWord).extract 0 32 = UInt256.toByteArray toWord := by
    have hread := delegateLoopKeyMem_read0 toWord senderWord
    rw [readWithPadding_eq_extract _ 0 (by rw [delegateLoopKeyMem_size]; omega)] at hread
    exact hread
  rw [hempty, ByteArray.empty_append, htoFull, htail]
  unfold delegateLoopHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega)]
  rw [hkey0]
  rw [hbaseFull]
  rw [show 32 + 32 = 64 from rfl]
  rw [ByteArray.append_assoc]

theorem delegateLoopHashMem_writeBase (toWord senderWord : UInt256) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
        (delegateLoopHashMem toWord senderWord) 32 32 =
      delegateLoopHashMem toWord senderWord := by
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [delegateLoopHashMem_size]; omega)]
  have hhead :
      (delegateLoopHashMem toWord senderWord).extract 0 32 =
        UInt256.toByteArray toWord := by
    have hread := delegateLoopHashMem_read0 toWord senderWord
    rw [readWithPadding_eq_extract _ 0 (by rw [delegateLoopHashMem_size]; omega)] at hread
    exact hread
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have htail :
      (delegateLoopHashMem toWord senderWord).extract (32 + 32)
          (delegateLoopHashMem toWord senderWord).size =
        (delegateLoopKeyMem toWord senderWord).extract (32 + 32)
          (delegateLoopKeyMem toWord senderWord).size := by
    unfold delegateLoopHashMem
    rw [write32_eq _ _ 32 (by rw [toByteArray_size])
        (by rw [delegateLoopKeyMem_size]; omega)]
    rw [hbaseFull]
    rw [extract_append_right_window
      ((delegateLoopKeyMem toWord senderWord).extract 0 32 ++
        UInt256.toByteArray (⟨1⟩ : UInt256))
      ((delegateLoopKeyMem toWord senderWord).extract (32 + 32)
        (delegateLoopKeyMem toWord senderWord).size)
      (32 + 32)
      ((delegateLoopKeyMem toWord senderWord).extract 0 32 ++
        UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateLoopKeyMem toWord senderWord).extract (32 + 32)
          (delegateLoopKeyMem toWord senderWord).size).size
      (by
        rw [ByteArray.size_append, ByteArray.size_extract,
          delegateLoopKeyMem_size, toByteArray_size]
        norm_num)]
    have hprefixSize :
        ((delegateLoopKeyMem toWord senderWord).extract 0 32 ++
          UInt256.toByteArray (⟨1⟩ : UInt256)).size = 64 := by
      rw [ByteArray.size_append, ByteArray.size_extract, delegateLoopKeyMem_size,
        toByteArray_size]
      norm_num
    simpa [hprefixSize, ByteArray.size_append] using byteArray_extract_self
      ((delegateLoopKeyMem toWord senderWord).extract (32 + 32)
        (delegateLoopKeyMem toWord senderWord).size)
  rw [hhead, hbaseFull, htail]
  unfold delegateLoopHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega)]
  have hkey0 :
      (delegateLoopKeyMem toWord senderWord).extract 0 32 = UInt256.toByteArray toWord := by
    have hread := delegateLoopKeyMem_read0 toWord senderWord
    rw [readWithPadding_eq_extract _ 0 (by rw [delegateLoopKeyMem_size]; omega)] at hread
    exact hread
  rw [hkey0]
  rw [hbaseFull]

theorem delegateSenderKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((delegateHashMem (delegateSourceWord I)).readWithPadding 0 64)))
      = delegateSenderSlot I := by
  rw [delegateHashMem_read0_64]
  unfold delegateSenderSlot voterBase mapSlot
  rw [show keyValueToWord (.address I.source) = delegateSourceWord I by
    simpa [delegateSourceWord] using keyValueToWord_address I.source]
  exact mappingSlot_single (delegateSourceWord I) ⟨1⟩

theorem delegateVoterKeccakSlot (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((delegateHashMem w).readWithPadding 0 64)))
      = delegateVoterSlot w := by
  rw [delegateHashMem_read0_64]
  unfold delegateVoterSlot voterBase mapSlot
  rw [keyValueToWord_address_of_canonical w hcanon]
  exact mappingSlot_single w ⟨1⟩

theorem delegateLoopVoterKeccakSlot (toWord senderWord : UInt256)
    (hcanon : toWord.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((delegateLoopHashMem toWord senderWord).readWithPadding 0 64)))
      = delegateVoterSlot toWord := by
  rw [delegateLoopHashMem_read0_64]
  unfold delegateVoterSlot voterBase mapSlot
  rw [keyValueToWord_address_of_canonical toWord hcanon]
  exact mappingSlot_single toWord ⟨1⟩

theorem delegateProposalsDataBaseKeccak (toWord senderWord : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((delegateProposalBaseMem toWord senderWord).readWithPadding 0 32))) =
      proposalsDataBase := by
  rw [delegateProposalBaseMem_read0]
  unfold proposalsDataBase
  exact keccakSlot_eq _

theorem delegateOverflowGt (target addend : UInt256)
    (hover : UInt256.size ≤ target.toNat + addend.toNat) :
    UInt256.gt target (addend + target) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ addend.toNat + target.toNat := by
    omega
  have hsum_lt2 : addend.toNat + target.toNat < 2 * UInt256.size := by
    have ht : target.toNat < UInt256.size := target.val.isLt
    have ha : addend.toNat < UInt256.size := addend.val.isLt
    omega
  have hmod : (addend.toNat + target.toNat) % UInt256.size =
      addend.toNat + target.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (addend + target).toNat = addend.toNat + target.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (target > addend + target)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show target.toNat > (addend + target).toNat
    rw [haddNat]
    have ha : addend.toNat < UInt256.size := addend.val.isLt
    omega

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Ballot

/-! ### Delegate-local decoder routines -/

-- SHARED HELPER CANDIDATE: `Examples/Ballot/Common.lean` or a future `Routines.lean`.
theorem RD.ballotDelegateDecodeAddrOk1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨0⟩)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
      < EVM.addressModulus)
    (hret : (D_J ballotBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  have rd1786 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run rd1786 with [
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩,
    jumpiT (by
      change UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            solcAddrMask) ≠ ⟨0⟩
      rw [hclean]
      decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump hret ]⟩

theorem RD.ballotDelegateDecodeAddrLenRevert1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev ballotBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem RD.ballotDelegateDecodeAddrNoncanonRevert1770 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨0⟩)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have rd1786 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  exact (evm_run rd1786 with [
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩,
    jumpiNT (by
      change UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            solcAddrMask) = ⟨0⟩
      exact hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev ballotBytecode g s0)

end Reasoning.Reach

namespace Ballot

/-! ### EVM traces through the first delegate guard -/

theorem ballotDelegateX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1770⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨259⟩, ⟨156⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd245⟩ := hreach
  exact ⟨_, _, evm_run rd245 with [
    jumpdest, push2 ⟨156⟩, push2 ⟨259⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1770⟩, jump (by jump_dest) ]⟩

theorem ballotDelegateX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨715⟩
      [delegateToWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotDelegateX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  obtain ⟨_, _, rd259⟩ := RD.ballotDelegateDecodeAddrOk1770
    (R := [⟨156⟩, sel]) rd1770 hslt hcanon (by jump_dest) (by norm_num)
  exact ⟨_, _, evm_run rd259 with [jumpdest, push2 ⟨715⟩, jump (by jump_dest)]⟩

theorem ballotDelegateX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1770⟩ := ballotDelegateX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDelegateDecodeAddrLenRevert1770 (R := [⟨156⟩, sel]) rd1770 hslt (by norm_num)

theorem ballotDelegateX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1770⟩ := ballotDelegateX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDelegateDecodeAddrLenRevert1770 (R := [⟨156⟩, sel]) rd1770 hslt (by norm_num)

theorem ballotDelegateX_decodeRevert_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (delegateToWord I) (UInt256.land (delegateToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotDelegateX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDelegateDecodeAddrNoncanonRevert1770
    (R := [⟨156⟩, sel]) rd1770 hslt hnc (by norm_num)

theorem ballotDelegateX_afterWeight {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨810⟩
      [delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd715⟩ := ballotDelegateX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have hslot := delegateSenderKeccakSlot I
  have rd729 := evm_run rd715 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (delegateKeyMem (delegateSourceWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (delegateSenderSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨_, _, rd732₀⟩ := rd729.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd732⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨732⟩
      [delegateSenderWeightWord σ I, delegateSenderSlot I, ⟨0⟩, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using rd732₀⟩
  have rd735 := evm_run rd732 with [swap1, swap2, sub]
  have hneq :
      UInt256.sub ⟨0⟩ (delegateSenderWeightWord σ I) ≠ ⟨0⟩ :=
    u256_zero_sub_ne_zero hweight
  exact ⟨_, _, evm_run rd735 with [push2 ⟨810⟩, jumpiT hneq (by jump_dest)]⟩

theorem ballotDelegateX_weightRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd715⟩ := ballotDelegateX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have hslot := delegateSenderKeccakSlot I
  have rd729 := evm_run rd715 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (delegateKeyMem (delegateSourceWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (delegateSenderSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨_, _, rd732₀⟩ := rd729.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd732⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨732⟩
      [delegateSenderWeightWord σ I, delegateSenderSlot I, ⟨0⟩, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using rd732₀⟩
  have rd735 := evm_run rd732 with [swap1, swap2, sub]
  have hsubzero : UInt256.sub ⟨0⟩ (delegateSenderWeightWord σ I) = ⟨0⟩ := by
    rw [hweight]
    decide
  have rd735' := rd735
  rw [hsubzero] at rd735'
  have rd739 := evm_run rd735' with [push2 ⟨810⟩, jumpiNT (by decide)]
  have rd742 := evm_run rd739 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (delegateHashMem_mload64 (delegateSourceWord I)) (by decide) (by evm_ov) ]
  have rd746 := rd742.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd765 := evm_run rd746 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (delegateWeightErrorMem0 (delegateSourceWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (delegateWeightErrorMem1 (delegateSourceWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨25⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (delegateWeightErrorMem2 (delegateSourceWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd798 := rd765.pushConst delegateWeightStringWord (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd798 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (delegateWeightErrorMem3 (delegateSourceWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (delegateWeightErrorMem3_mload64 (delegateSourceWord I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

theorem ballotDelegateX_afterNotVoted {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨884⟩
      [delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd810⟩ := ballotDelegateX_afterWeight (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hreach
  have rd815₀ := evm_run rd810 with [jumpdest, push1 ⟨1⟩, dup2, add]
  obtain ⟨_, _, rd816₀⟩ := rd815₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd816⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [delegateSenderPackedWord σ I, delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderPackedWord, delegateSenderPackedSlot, delegateSenderSlot, initState]
        using rd816₀⟩
  have rd819 := evm_run rd816 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (delegateSenderPackedWord σ I)) = ⟨1⟩ := by
    change UInt256.isZero (delegateSenderVotedByte σ I) = ⟨1⟩
    rw [hvoted]
    decide
  have rd819' := rd819
  rw [hzero] at rd819'
  exact ⟨_, _, evm_run rd819' with [push2 ⟨884⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_votedRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd810⟩ := ballotDelegateX_afterWeight (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hreach
  have rd815₀ := evm_run rd810 with [jumpdest, push1 ⟨1⟩, dup2, add]
  obtain ⟨_, _, rd816₀⟩ := rd815₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd816⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [delegateSenderPackedWord σ I, delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderPackedWord, delegateSenderPackedSlot, delegateSenderSlot, initState]
        using rd816₀⟩
  have rd819 := evm_run rd816 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (delegateSenderPackedWord σ I)) = ⟨0⟩ := by
    change UInt256.isZero (delegateSenderVotedByte σ I) = ⟨0⟩
    exact isZero_eq_zero_of_ne hvoted
  have rd819' := rd819
  rw [hzero] at rd819'
  have rd824 := evm_run rd819' with [push2 ⟨884⟩, jumpiNT (by decide)]
  have rd827 := evm_run rd824 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (delegateHashMem_mload64 (delegateSourceWord I)) (by decide) (by evm_ov) ]
  have rd831 := rd827.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd850 := evm_run rd831 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (delegateWeightErrorMem0 (delegateSourceWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (delegateWeightErrorMem1 (delegateSourceWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨18⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (delegateVotedErrorMem2 (delegateSourceWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd869 := rd850.pushConst delegateVotedStringRaw (width := 18) (op := .PUSH18)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd869 with [
    push1 ⟨113⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3 (delegateVotedErrorMem3 (delegateSourceWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (delegateVotedErrorMem3_mload64 (delegateSourceWord I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

theorem ballotDelegateX_selfRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hself : delegateToWord I = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd884⟩ := ballotDelegateX_afterNotVoted (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hreach
  have hdiff :
      UInt256.sub
        (UInt256.land (delegateToWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (UInt256.ofNat I.source.val) = ⟨0⟩ := by
    change UInt256.sub (UInt256.land (delegateToWord I) solcAddrMask)
        (delegateSourceWord I) = ⟨0⟩
    rw [solcAddrMask_clean hcanon, hself]
    exact u256_sub_self (delegateSourceWord I)
  have rd897 := evm_run rd884 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and, sub ]
  have rd897' := rd897
  rw [hdiff] at rd897'
  have rd901 := evm_run rd897' with [push2 ⟨972⟩, jumpiNT (by decide)]
  have rd904 := evm_run rd901 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (delegateHashMem_mload64 (delegateSourceWord I)) (by decide) (by evm_ov) ]
  have rd908 := rd904.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd927 := evm_run rd908 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (delegateWeightErrorMem0 (delegateSourceWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (delegateWeightErrorMem1 (delegateSourceWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨30⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (delegateSelfErrorMem2 (delegateSourceWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd960 := rd927.pushConst delegateSelfStringWord (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd960 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (delegateSelfErrorMem3 (delegateSourceWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (delegateSelfErrorMem3_mload64 (delegateSourceWord I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

theorem ballotDelegateX_afterNotSelf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd884⟩ := ballotDelegateX_afterNotVoted (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hreach
  have hdiff :
      UInt256.sub
        (UInt256.land (delegateToWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (UInt256.ofNat I.source.val) ≠ ⟨0⟩ := by
    change UInt256.sub (UInt256.land (delegateToWord I) solcAddrMask)
        (delegateSourceWord I) ≠ ⟨0⟩
    rw [solcAddrMask_clean hcanon]
    exact u256_sub_ne_zero_of_ne hnotself
  have rd897 := evm_run rd884 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and, sub ]
  exact ⟨_, _, evm_run rd897 with [push2 ⟨972⟩, jumpiT hdiff (by jump_dest)]⟩

theorem ballotDelegateX_loopExit {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := ballotDelegateX_afterNotSelf (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hnotself hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask (delegateToWord I))).write 0
            (delegateHashMem (delegateSourceWord I)) 0 32 =
          delegateLoopKeyMem (delegateToWord I) (delegateSourceWord I)
        rw [u256_land_comm solcAddrMask (delegateToWord I)]
        rw [solcAddrMask_clean hcanon]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot (delegateToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (delegateLoopVoterKeccakSlot (delegateToWord I) (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I (delegateToWord I),
        solcAddrMask, delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm]
        using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.div rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land
            (UInt256.div (delegateVoterPackedWord σ I (delegateToWord I)) ⟨256⟩) solcAddrMask) =
        ⟨1⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I (delegateToWord I)) = ⟨1⟩
    rw [hdelegate]
    decide
  have rd1008' := rd1008
  rw [hzero] at rd1008'
  exact ⟨_, _, evm_run rd1008' with [push2 ⟨1134⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_afterDelegateWeight {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
      [delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1134⟩ := ballotDelegateX_loopExit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hnotself hdelegate hreach
  have hslot := delegateLoopVoterKeccakSlot (delegateToWord I) (delegateSourceWord I) hcanon
  have rd1160 := evm_run rd1134 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land (delegateToWord I) solcAddrMask)).write 0
            (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) 0 32 =
          delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)
        rw [solcAddrMask_clean hcanon]
        exact delegateLoopHashMem_writeKey (delegateToWord I) (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (delegateLoopHashMem_writeBase (delegateToWord I) (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot (delegateToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  have rd1162 := evm_run rd1160 with [dup1]
  obtain ⟨_, _, rd1163₀⟩ := rd1162.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1163⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
      [delegateVoterWeightWord σ I (delegateToWord I), delegateVoterSlot (delegateToWord I),
        ⟨1⟩, delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterWeightWord, delegateVoterSlot, initState] using rd1163₀⟩
  have rd1167 := evm_run rd1163 with [swap1, swap2, gt, iszero]
  have hweightNat : 1 ≤ (delegateVoterWeightWord σ I (delegateToWord I)).toNat := by
    have hnz : (delegateVoterWeightWord σ I (delegateToWord I)).toNat ≠ 0 := by
      intro hzero
      apply hdelegateWeight
      apply u256_inj
      exact hzero
    omega
  have hgt :
      UInt256.gt (⟨1⟩ : UInt256) (delegateVoterWeightWord σ I (delegateToWord I)) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by
      change 1 ≤ (delegateVoterWeightWord σ I (delegateToWord I)).toNat
      exact hweightNat)
  have rd1167' := rd1167
  rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1167'
  exact ⟨_, _, evm_run rd1167' with [push2 ⟨1174⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_delegateWeightRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1134⟩ := ballotDelegateX_loopExit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hnotself hdelegate hreach
  have hslot := delegateLoopVoterKeccakSlot (delegateToWord I) (delegateSourceWord I) hcanon
  have rd1160 := evm_run rd1134 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land (delegateToWord I) solcAddrMask)).write 0
            (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) 0 32 =
          delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)
        rw [solcAddrMask_clean hcanon]
        exact delegateLoopHashMem_writeKey (delegateToWord I) (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (delegateLoopHashMem_writeBase (delegateToWord I) (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot (delegateToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  have rd1162 := evm_run rd1160 with [dup1]
  obtain ⟨_, _, rd1163₀⟩ := rd1162.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1163⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
      [delegateVoterWeightWord σ I (delegateToWord I), delegateVoterSlot (delegateToWord I),
        ⟨1⟩, delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterWeightWord, delegateVoterSlot, initState] using rd1163₀⟩
  have rd1167 := evm_run rd1163 with [swap1, swap2, gt, iszero]
  have hgt :
      UInt256.gt (⟨1⟩ : UInt256) (delegateVoterWeightWord σ I (delegateToWord I)) = ⟨1⟩ := by
    rw [hdelegateWeight]
    decide
  have rd1167' := rd1167
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1167'
  have rd1171 := evm_run rd1167' with [push2 ⟨1174⟩, jumpiNT (by decide)]
  exact rd1171.revertStub (by decide) (by decide) (by decide) (by evm_ov)

theorem ballotDelegateX_afterSenderPackedStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I,
        ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1174⟩ := ballotDelegateX_afterDelegateWeight (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hweight hvoted hnotself hdelegate hdelegateWeight hreach
  have rd1181 := evm_run rd1174 with [jumpdest, push1 ⟨1⟩, dup3, dup2, add, dup1]
  obtain ⟨_, _, rd1182₀⟩ := rd1181.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1182⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1182⟩
      [delegateSenderPackedWord σ I, delegateSenderPackedSlot I, ⟨1⟩,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderPackedWord, delegateSenderPackedSlot, initState, u256_add_comm]
        using rd1182₀⟩
  have rd1205 := evm_run rd1182 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨168⟩, shl, sub, not, and,
    push2 ⟨256⟩, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and, mul ]
  have rd1207 := RD.lor rd1205 (by decide) (by evm_ov)
  have rd1208 := evm_run rd1207 with [dup3]
  have rd1209 := RD.lor rd1208 (by decide) (by evm_ov)
  have rd1210 := evm_run rd1209 with [swap1]
  obtain ⟨_, _, rd1211⟩ := rd1210.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [delegateAfterSenderMap, delegateSenderPackedStoreWord, delegateSenderPackedWord,
      delegateSenderPackedSlot, initState] using rd1211⟩

theorem ballotDelegateX_delegateNotVotedBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1285⟩
      [delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1211⟩ := ballotDelegateX_afterSenderPackedStore (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight hreach
  have rd1213 := evm_run rd1211 with [dup2, add]
  obtain ⟨_, _, rd1214₀⟩ := rd1213.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1214⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1214⟩
      [delegateVoterPackedWord (delegateAfterSenderMap σ I) I (delegateToWord I),
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot] using rd1214₀⟩
  have rd1218 := evm_run rd1214 with [push1 ⟨255⟩, and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land ⟨255⟩
            (delegateVoterPackedWord (delegateAfterSenderMap σ I) I (delegateToWord I))) =
        ⟨1⟩ := by
    change UInt256.isZero
        (delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I)) = ⟨1⟩
    rw [hdelegateNotVoted]
    decide
  have rd1218' := rd1218
  rw [hzero] at rd1218'
  exact ⟨_, _, evm_run rd1218' with [push2 ⟨1285⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_delegateVotedBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1222⟩
      [delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1211⟩ := ballotDelegateX_afterSenderPackedStore (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight hreach
  have rd1213 := evm_run rd1211 with [dup2, add]
  obtain ⟨_, _, rd1214₀⟩ := rd1213.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1214⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1214⟩
      [delegateVoterPackedWord (delegateAfterSenderMap σ I) I (delegateToWord I),
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot] using rd1214₀⟩
  have rd1218 := evm_run rd1214 with [push1 ⟨255⟩, and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land ⟨255⟩
            (delegateVoterPackedWord (delegateAfterSenderMap σ I) I (delegateToWord I))) =
        ⟨0⟩ := by
    change UInt256.isZero
        (delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I)) = ⟨0⟩
    exact isZero_eq_zero_of_ne hdelegateVoted
  have rd1218' := rd1218
  rw [hzero] at rd1218'
  exact ⟨_, _, evm_run rd1218' with [push2 ⟨1285⟩, jumpiNT (by decide)]⟩

theorem ballotDelegateX_delegateNotVotedToCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1835⟩
      [delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I),
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I, ⟨1304⟩, ⟨0⟩,
        delegateVoterSlot (delegateToWord I),
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩,
        sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1285⟩ := ballotDelegateX_delegateNotVotedBranch (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
    hdelegateNotVoted hreach
  have rd1287 := evm_run rd1285 with [jumpdest, dup2]
  obtain ⟨_, _, rd1288₀⟩ := rd1287.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1288⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1288⟩
      [delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by simpa [delegateSenderWeightWord, initState] using rd1288₀⟩
  have rd1289 := evm_run rd1288 with [dup2]
  obtain ⟨_, _, rd1290₀⟩ := rd1289.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1290⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1290⟩
      [delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I),
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by simpa [delegateVoterWeightWord, initState] using rd1290₀⟩
  exact ⟨_, _, evm_run rd1290 with [
    dup3, swap1, push0, swap1, push2 ⟨1304⟩, swap1, dup5, swap1, push2 ⟨1835⟩,
    jump (by jump_dest) ]⟩

theorem ballotDelegateX_delegateNotVotedAfterCheckedAdd {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1304⟩
      [delegateSenderWeightWord (delegateAfterSenderMap σ I) I +
          delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I),
        ⟨0⟩, delegateVoterSlot (delegateToWord I),
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩,
        sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_delegateNotVotedToCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateNotVoted hreach
  let target := delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)
  let addend := delegateSenderWeightWord (delegateAfterSenderMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hsumNat : (addend + target).toNat = addend.toNat + target.toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by simpa [target, addend, Nat.add_comm] using hfit)
  have hgt : UInt256.gt target (addend + target) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsumNat]; omega)
  have rd1842' := rd1842
  rw [show delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I) = target
        from rfl,
      show delegateSenderWeightWord (delegateAfterSenderMap σ I) I = addend from rfl, hgt,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1842'
  have rd1866 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiT (by decide) (by jump_dest)]
  have rd1304 := evm_run rd1866 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [target, addend] using rd1304⟩

theorem ballotDelegateX_delegateNotVotedSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, delegateFalseSuccessMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd1304⟩ := ballotDelegateX_delegateNotVotedAfterCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateNotVoted hfit hreach
  have rd1307 := evm_run rd1304 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1308⟩ := rd1307.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd1308 with [
    pop, pop, jumpdest, pop, pop, pop, jump (by jump_dest), jumpdest ]
  have hsum :
      delegateSenderWeightWord (delegateAfterSenderMap σ I) I +
          delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I) =
        delegateUpdatedVoterWeight σ I := by
    unfold delegateUpdatedVoterWeight
    exact u256_add_comm _ _
  exact by
    simpa [delegateFalseSuccessMap, hsum] using
      rd156.stop (by decide) (by evm_ov)

theorem ballotDelegateX_delegateNotVotedOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat +
        (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_delegateNotVotedToCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateNotVoted hreach
  let target := delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I)
  let addend := delegateSenderWeightWord (delegateAfterSenderMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hgt : UInt256.gt target (addend + target) = ⟨1⟩ := by
    exact delegateOverflowGt target addend (by simpa [target, addend] using hover)
  have rd1842' := rd1842
  rw [show delegateVoterWeightWord (delegateAfterSenderMap σ I) I (delegateToWord I) = target
        from rfl,
      show delegateSenderWeightWord (delegateAfterSenderMap σ I) I = addend from rfl, hgt,
      show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1842'
  have rd1847 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiNT (by decide)]
  exact RD.ballotPanic11Revert1847 rd1847
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotDelegateX_delegateVotedBoundsCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1234⟩
      [UInt256.lt (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I))
          (delegateProposalsLengthWord σ I),
        delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I), ⟨2⟩,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩,
        sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1222⟩ := ballotDelegateX_delegateVotedBranch (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
    hdelegateVoted hreach
  have rd1223 := evm_run rd1222 with [dup2]
  obtain ⟨_, _, rd1224₀⟩ := rd1223.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1224⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1224⟩
      [delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by simpa [delegateSenderWeightWord, initState] using rd1224₀⟩
  have rd1229 := evm_run rd1224 with [push1 ⟨2⟩, dup3, dup2, add]
  obtain ⟨_, _, rd1230₀⟩ := rd1229.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1230⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1230⟩
      [delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I), ⟨2⟩,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterVoteWord, delegateVoterVoteSlot, initState, u256_add_comm]
        using rd1230₀⟩
  have rd1231 := evm_run rd1230 with [dup2]
  obtain ⟨_, _, rd1232₀⟩ := rd1231.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1232⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1232⟩
      [delegateProposalsLengthWord σ I,
        delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I), ⟨2⟩,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateLoopHashMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by simpa [delegateProposalsLengthWord, initState] using rd1232₀⟩
  exact ⟨_, _, evm_run rd1232 with [dup2, lt]⟩

theorem ballotDelegateX_delegateVotedOob {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound : ¬
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1234⟩ := ballotDelegateX_delegateVotedBoundsCheck (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateVoted hreach
  have hlt :
      UInt256.lt (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I))
        (delegateProposalsLengthWord σ I) = ⟨0⟩ :=
    ult_zero (Nat.le_of_not_gt hbound)
  have rd1234' := rd1234
  rw [hlt] at rd1234'
  have rd1815 := evm_run rd1234' with [
    push2 ⟨1245⟩, jumpiNT (by decide), push2 ⟨1245⟩, push2 ⟨1815⟩,
    jump (by jump_dest) ]
  exact RD.ballotPanic32Revert1815 rd1815
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotDelegateX_delegateVotedToCheckedAdd {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1835⟩
      [delegateProposalCountWord σ I,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I, ⟨1274⟩, ⟨0⟩,
        delegateProposalCountSlot σ I,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩,
        sel]
      (delegateProposalBaseMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1234⟩ := ballotDelegateX_delegateVotedBoundsCheck (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateVoted hreach
  have hlt :
      UInt256.lt (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I))
        (delegateProposalsLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1234' := rd1234
  rw [hlt] at rd1234'
  have rd1245 := evm_run rd1234' with [push2 ⟨1245⟩, jumpiT (by decide) (by jump_dest)]
  have hbase := delegateProposalsDataBaseKeccak (delegateToWord I) (delegateSourceWord I)
  have rd1261 := evm_run rd1245 with [
    jumpdest, swap1, push0,
    raw mstore 0 (delegateProposalBaseMem (delegateToWord I) (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
      mem_cost hbase (by decide) (by evm_ov),
    swap1, push1 ⟨2⟩, mul, add, push1 ⟨1⟩, add ]
  have rd1264 := evm_run rd1261 with [push0, dup3, dup3]
  obtain ⟨_, _, rd1265₀⟩ := rd1264.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1265⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1265⟩
      [delegateProposalCountWord σ I,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I, ⟨0⟩,
        delegateProposalCountSlot σ I,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩, sel]
      (delegateProposalBaseMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
    exact ⟨_, _, by
      simpa [delegateProposalCountWord, delegateProposalCountSlot, initState] using rd1265₀⟩
  exact ⟨_, _, evm_run rd1265 with [
    push2 ⟨1274⟩, swap2, swap1, push2 ⟨1835⟩, jump (by jump_dest) ]⟩

theorem ballotDelegateX_delegateVotedAfterCheckedAdd {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ I).toNat)
    (hfit :
      (delegateProposalCountWord σ I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩
      [delegateSenderWeightWord (delegateAfterSenderMap σ I) I + delegateProposalCountWord σ I,
        ⟨0⟩, delegateProposalCountSlot σ I,
        delegateSenderWeightWord (delegateAfterSenderMap σ I) I,
        delegateVoterSlot (delegateToWord I), delegateSenderSlot I, delegateToWord I, ⟨156⟩,
        sel]
      (delegateProposalBaseMem (delegateToWord I) (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateAfterSenderMap σ I) k C := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_delegateVotedToCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateVoted hbound hreach
  let target := delegateProposalCountWord σ I
  let addend := delegateSenderWeightWord (delegateAfterSenderMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hsumNat : (addend + target).toNat = addend.toNat + target.toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by simpa [target, addend, Nat.add_comm] using hfit)
  have hgt : UInt256.gt target (addend + target) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsumNat]; omega)
  have rd1842' := rd1842
  rw [show delegateProposalCountWord σ I = target from rfl,
      show delegateSenderWeightWord (delegateAfterSenderMap σ I) I = addend from rfl, hgt,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1842'
  have rd1866 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiT (by decide) (by jump_dest)]
  have rd1274 := evm_run rd1866 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [target, addend] using rd1274⟩

theorem ballotDelegateX_delegateVotedSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ I).toNat)
    (hfit :
      (delegateProposalCountWord σ I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, delegateTrueSuccessMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd1274⟩ := ballotDelegateX_delegateVotedAfterCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateVoted hbound hfit hreach
  have rd1277 := evm_run rd1274 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1278⟩ := rd1277.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd1278 with [
    pop, push2 ⟨1310⟩, swap1, pop, jump (by jump_dest), jumpdest, pop, pop, pop,
    jump (by jump_dest), jumpdest ]
  have hsum :
      delegateSenderWeightWord (delegateAfterSenderMap σ I) I + delegateProposalCountWord σ I =
        delegateUpdatedProposalCount σ I := by
    unfold delegateUpdatedProposalCount
    exact u256_add_comm _ _
  exact by
    simpa [delegateTrueSuccessMap, hsum] using rd156.stop (by decide) (by evm_ov)

theorem ballotDelegateX_delegateVotedOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ I).toNat)
    (hover : UInt256.size ≤
      (delegateProposalCountWord σ I).toNat +
        (delegateSenderWeightWord (delegateAfterSenderMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_delegateVotedToCheckedAdd (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hszhi hperm hcanon hweight hvoted hnotself hdelegate
    hdelegateWeight hdelegateVoted hbound hreach
  let target := delegateProposalCountWord σ I
  let addend := delegateSenderWeightWord (delegateAfterSenderMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hgt : UInt256.gt target (addend + target) = ⟨1⟩ := by
    exact delegateOverflowGt target addend (by simpa [target, addend] using hover)
  have rd1842' := rd1842
  rw [show delegateProposalCountWord σ I = target from rfl,
      show delegateSenderWeightWord (delegateAfterSenderMap σ I) I = addend from rfl, hgt,
      show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1842'
  have rd1847 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiNT (by decide)]
  exact RD.ballotPanic11Revert1847 rd1847
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotDelegateSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_delegate {cd : ByteArray}
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some delegateTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [voteTransition, proposalsGetter, chairpersonGetter])
    (post := [winningProposalTransition, giveRightToVoteTransition, votersGetter,
      winnerNameTransition])
    rfl ?_ (by rw [selectorOf, ballotDelegateSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotChairpersonSelectorBytes, hcd]; decide

theorem ballotDelegateWeightRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hbody := ballotDelegateBodyReverts_weight
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      have hweightSolm : delegateSenderWeightWord σ_solm I = ⟨0⟩ := by
        simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
      simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using hweightSolm)
  exact (ballotDelegateX_weightRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hcanon hweight hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateVotedRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hbody := ballotDelegateBodyReverts_voted
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
        simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
      simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using hweightSolm)
    (by
      have hvotedSolm : delegateSenderVotedByte σ_solm I ≠ ⟨0⟩ := by
        simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted
      intro hz
      apply hvotedSolm
      have hcomm :
          UInt256.land ⟨255⟩ (delegateSenderPackedWord σ_solm I) =
            UInt256.land (delegateSenderPackedWord σ_solm I) ⟨255⟩ :=
        u256_land_comm ⟨255⟩ (delegateSenderPackedWord σ_solm I)
      change UInt256.land ⟨255⟩ (delegateSenderPackedWord σ_solm I) = ⟨0⟩
      rw [hcomm]
      simpa [delegateSenderPackedWord, delegateSenderPackedSlot, delegateSenderSlot, initState]
        using hz)
  exact (ballotDelegateX_votedRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hcanon hweight hvoted hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateSelfRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hself : delegateToWord I = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hbody := ballotDelegateBodyReverts_self
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
        simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
      simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using hweightSolm)
    (by
      have hvotedSolm : delegateSenderVotedByte σ_solm I = ⟨0⟩ := by
        simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted
      change UInt256.land (delegateSenderPackedWord σ_solm I) ⟨255⟩ = ⟨0⟩
      rw [u256_land_comm (delegateSenderPackedWord σ_solm I) ⟨255⟩]
      exact hvotedSolm)
    hself
  exact (ballotDelegateX_selfRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hcanon hweight hvoted hself hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateDelegateWeightRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hbody := ballotDelegateBodyReverts_delegateWeight
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by
      rw [delegateSenderWeightCurrent_init]
      exact (by simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
  exact (ballotDelegateX_delegateWeightRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hcanon hweight hvoted hnotself hdelegate hdelegateWeight hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateNotVotedSuccessEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I (delegateToWord I) = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateAfterSenderMap σ_evm I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hafter := delegateAfterSenderMap_accountMapEquiv (I := I) hAccounts
  have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
    simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
  have hfitSolm :
      (delegateVoterWeightWord (delegateAfterSenderMap σ_solm I) I (delegateToWord I)).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ_solm I) I).toNat <
        UInt256.size := by
    simpa [← delegateVoterWeightWord_accountMapEquiv hafter (delegateToWord I),
      ← delegateSenderWeightWord_accountMapEquiv hafter] using hfit
  have hbody := ballotDelegateBodyReturns_notVoted
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by rw [delegateSenderWeightCurrent_init]; exact hweightSolm)
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
    (by
      rw [delegateVoterVotedByteCurrent_afterSenderState_init]
      exact (by
        simpa [← delegateVoterVotedByte_accountMapEquiv hafter (delegateToWord I)]
          using hdelegateNotVoted))
    (by
      rw [delegateVoterWeightCurrent_afterSenderState_init,
        delegateSenderWeightCurrent_afterSenderState_init]
      exact hfitSolm)
  exact (ballotDelegateX_delegateNotVotedSuccess (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
      hdelegateNotVoted hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
      (delegateFalseSuccessState_created_init (g := Sat256.ofUInt256 g) (σ := σ_evm))
      (delegateFalseSuccessState_accountMapEquiv_init
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) hweight hfit)
      (delegateFalseSuccessState_EVMStateEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) hAccounts)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateVotedSuccessEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ_evm I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ_evm I).toNat)
    (hfit :
      (delegateProposalCountWord σ_evm I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hafter := delegateAfterSenderMap_accountMapEquiv (I := I) hAccounts
  have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
    simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
  have hboundSolm :
      (delegateVoterVoteWord (delegateAfterSenderMap σ_solm I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ_solm I).toNat := by
    simpa [← delegateVoterVoteWord_accountMapEquiv hafter (delegateToWord I),
      ← delegateProposalsLengthWord_accountMapEquiv hAccounts] using hbound
  have hfitSolm :
      (delegateProposalCountWord σ_solm I).toNat +
          (delegateSenderWeightWord (delegateAfterSenderMap σ_solm I) I).toNat <
        UInt256.size := by
    simpa [← delegateProposalCountWord_accountMapEquiv hAccounts,
      ← delegateSenderWeightWord_accountMapEquiv hafter] using hfit
  have hbody := ballotDelegateBodyReturns_voted
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by rw [delegateSenderWeightCurrent_init]; exact hweightSolm)
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
    (by
      rw [delegateVoterVotedByteCurrent_afterSenderState_init]
      exact (by
        simpa [← delegateVoterVotedByte_accountMapEquiv hafter (delegateToWord I)]
          using hdelegateVoted))
    (by
      rw [delegateVoterVoteCurrent_afterSenderState_init,
        delegateProposalsLengthCurrent_afterSenderState_init]
      exact hboundSolm)
    (by
      rw [delegateProposalCountCurrent_init,
        delegateSenderWeightCurrent_afterSenderState_init]
      exact hfitSolm)
  exact (ballotDelegateX_delegateVotedSuccess (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
      hdelegateVoted hbound hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
      (delegateTrueSuccessState_created_init (g := Sat256.ofUInt256 g) (σ := σ_evm))
      (delegateTrueSuccessState_accountMapEquiv_init
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) hweight hfit)
      (delegateTrueSuccessState_EVMStateEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) hAccounts)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateNotVotedOverflowEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I (delegateToWord I) = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateVoterWeightWord (delegateAfterSenderMap σ_evm I) I (delegateToWord I)).toNat +
        (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hafter := delegateAfterSenderMap_accountMapEquiv (I := I) hAccounts
  have hbody := ballotDelegateBodyReverts_notVotedOverflow
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by
      rw [delegateSenderWeightCurrent_init]
      exact (by simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
    (by
      rw [delegateVoterVotedByteCurrent_afterSenderState_init]
      exact (by
        simpa [← delegateVoterVotedByte_accountMapEquiv hafter (delegateToWord I)]
          using hdelegateNotVoted))
    (by
      rw [delegateVoterWeightCurrent_afterSenderState_init,
        delegateSenderWeightCurrent_afterSenderState_init]
      simpa [← delegateVoterWeightWord_accountMapEquiv hafter (delegateToWord I),
        ← delegateSenderWeightWord_accountMapEquiv hafter] using hover)
  exact (ballotDelegateX_delegateNotVotedOverflow (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
      hdelegateNotVoted hover hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateVotedOobEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound : ¬
      (delegateVoterVoteWord (delegateAfterSenderMap σ_evm I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ_evm I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hafter := delegateAfterSenderMap_accountMapEquiv (I := I) hAccounts
  have hbody := ballotDelegateBodyReverts_votedOob
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by
      rw [delegateSenderWeightCurrent_init]
      exact (by simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
    (by
      rw [delegateVoterVotedByteCurrent_afterSenderState_init]
      exact (by
        simpa [← delegateVoterVotedByte_accountMapEquiv hafter (delegateToWord I)]
          using hdelegateVoted))
    (by
      rw [delegateVoterVoteCurrent_afterSenderState_init,
        delegateProposalsLengthCurrent_afterSenderState_init]
      simpa [← delegateVoterVoteWord_accountMapEquiv hafter (delegateToWord I),
        ← delegateProposalsLengthWord_accountMapEquiv hAccounts] using hbound)
  exact (ballotDelegateX_delegateVotedOob (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
      hdelegateVoted hbound hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateVotedOverflowEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hdelegate : delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩)
    (hdelegateWeight : delegateVoterWeightWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I (delegateToWord I) ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateAfterSenderMap σ_evm I) I (delegateToWord I)).toNat <
        (delegateProposalsLengthWord σ_evm I).toNat)
    (hover : UInt256.size ≤
      (delegateProposalCountWord σ_evm I).toNat +
        (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hafter := delegateAfterSenderMap_accountMapEquiv (I := I) hAccounts
  have hbody := ballotDelegateBodyReverts_votedOverflow
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by
      rw [delegateSenderWeightCurrent_init]
      exact (by simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [delegateSenderVotedByteCurrent_init]
      exact (by simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    hnotself
    (by
      rw [delegateVoterDelegateWordCurrent_init]
      exact (by
        simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegate))
    (by
      rw [delegateVoterWeightCurrent_init]
      exact (by
        simpa [← delegateVoterWeightWord_accountMapEquiv hAccounts (delegateToWord I)]
          using hdelegateWeight))
    (by
      rw [delegateVoterVotedByteCurrent_afterSenderState_init]
      exact (by
        simpa [← delegateVoterVotedByte_accountMapEquiv hafter (delegateToWord I)]
          using hdelegateVoted))
    (by
      rw [delegateVoterVoteCurrent_afterSenderState_init,
        delegateProposalsLengthCurrent_afterSenderState_init]
      simpa [← delegateVoterVoteWord_accountMapEquiv hafter (delegateToWord I),
        ← delegateProposalsLengthWord_accountMapEquiv hAccounts] using hbound)
    (by
      rw [delegateProposalCountCurrent_init,
        delegateSenderWeightCurrent_afterSenderState_init]
      simpa [← delegateProposalCountWord_accountMapEquiv hAccounts,
        ← delegateSenderWeightWord_accountMapEquiv hafter] using hover)
  exact (ballotDelegateX_delegateVotedOverflow (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hcanon hweight hvoted hnotself hdelegate hdelegateWeight
      hdelegateVoted hbound hover hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateDecodeShortEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ballotDelegateSelector_size hsel
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_none_short (I := I) hsz4 hshort
  exact (ballotDelegateX_decodeRevert_short (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hd hdec

theorem ballotDelegateDecodeHugeEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_none_huge (I := I) hbig
  exact (ballotDelegateX_decodeRevert_huge (g := Sat256.ofUInt256 g) hsize hbig hreach)
    |>.reEquivDecodingFailed hcode hd hdec

theorem ballotDelegateDecodeNoncanonEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (delegateToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_none_noncanon (I := I) hsz36 hbig hnc
  have hclean :
      UInt256.eq (delegateToWord I) (UInt256.land (delegateToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnc (solcAddrCanonical_of_clean he))
  exact (ballotDelegateX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hclean hreach)
    |>.reEquivDecodingFailed hcode hd hdec

theorem ballotDelegateBodyCoreFrontier
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsuccess :
      36 ≤ I.calldata.size →
      I.calldata.size < 2 ^ 255 + 4 →
      (delegateToWord I).toNat < EVM.addressModulus →
      delegateSenderWeightWord σ_evm I ≠ ⟨0⟩ →
      delegateSenderVotedByte σ_evm I = ⟨0⟩ →
      delegateToWord I ≠ delegateSourceWord I →
      I.perm = true →
      delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ ⟨0⟩ →
      runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
        σ_evm σ_solm σ₀ g A I) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (delegateToWord I).toNat < EVM.addressModulus
      · by_cases hweight : delegateSenderWeightWord σ_evm I = ⟨0⟩
        · exact ballotDelegateWeightRevertEquiv hcode hsize hwv hsel hsz36 hbig hcanon hweight
            hreach hAccounts
        · by_cases hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩
          · by_cases hself : delegateToWord I = delegateSourceWord I
            · exact ballotDelegateSelfRevertEquiv hcode hsize hwv hsel hsz36 hbig hcanon hweight
                hvoted hself hreach hAccounts
            · by_cases hdelegate :
                delegateVoterDelegateWord σ_evm I (delegateToWord I) = ⟨0⟩
              · by_cases hdelegateWeight :
                  delegateVoterWeightWord σ_evm I (delegateToWord I) = ⟨0⟩
                · exact ballotDelegateDelegateWeightRevertEquiv hcode hsize hwv hsel hsz36 hbig
                    hcanon hweight hvoted hself hdelegate hdelegateWeight hreach hAccounts
                · by_cases hdelegateNotVoted :
                    delegateVoterVotedByte (delegateAfterSenderMap σ_evm I) I
                      (delegateToWord I) = ⟨0⟩
                  · by_cases hfit :
                      (delegateVoterWeightWord (delegateAfterSenderMap σ_evm I) I
                          (delegateToWord I)).toNat +
                          (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat <
                        UInt256.size
                    · exact ballotDelegateNotVotedSuccessEquiv hcode hsize hwv hperm hsel
                        hsz36 hbig hcanon hweight hvoted hself hdelegate hdelegateWeight
                        hdelegateNotVoted hfit hreach hAccounts
                    · have hover :
                        UInt256.size ≤
                          (delegateVoterWeightWord (delegateAfterSenderMap σ_evm I) I
                              (delegateToWord I)).toNat +
                            (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat := by
                        omega
                      exact ballotDelegateNotVotedOverflowEquiv hcode hsize hwv hperm hsel
                        hsz36 hbig hcanon hweight hvoted hself hdelegate hdelegateWeight
                        hdelegateNotVoted hover hreach hAccounts
                  · by_cases hbound :
                      (delegateVoterVoteWord (delegateAfterSenderMap σ_evm I) I
                          (delegateToWord I)).toNat <
                        (delegateProposalsLengthWord σ_evm I).toNat
                    · by_cases hfit :
                        (delegateProposalCountWord σ_evm I).toNat +
                            (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat <
                          UInt256.size
                      · exact ballotDelegateVotedSuccessEquiv hcode hsize hwv hperm hsel hsz36
                          hbig hcanon hweight hvoted hself hdelegate hdelegateWeight
                          hdelegateNotVoted hbound hfit hreach hAccounts
                      · have hover :
                          UInt256.size ≤
                            (delegateProposalCountWord σ_evm I).toNat +
                              (delegateSenderWeightWord (delegateAfterSenderMap σ_evm I) I).toNat := by
                          omega
                        exact ballotDelegateVotedOverflowEquiv hcode hsize hwv hperm hsel hsz36
                          hbig hcanon hweight hvoted hself hdelegate hdelegateWeight
                          hdelegateNotVoted hbound hover hreach hAccounts
                    · exact ballotDelegateVotedOobEquiv hcode hsize hwv hperm hsel hsz36 hbig
                        hcanon hweight hvoted hself hdelegate hdelegateWeight hdelegateNotVoted
                        hbound hreach hAccounts
              · exact hsuccess hsz36 hbig hcanon hweight hvoted hself hperm hdelegate
          · exact ballotDelegateVotedRevertEquiv hcode hsize hwv hsel hsz36 hbig hcanon hweight
              hvoted hreach hAccounts
      · exact ballotDelegateDecodeNoncanonEquiv hcode hsize hsel hsz36 hbig hcanon hreach
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact ballotDelegateDecodeHugeEquiv hcode hsize hsel hbigge hreach
  · have hshort : I.calldata.size < 36 := by omega
    exact ballotDelegateDecodeShortEquiv hcode hsize hsel hshort hreach

end Ballot
