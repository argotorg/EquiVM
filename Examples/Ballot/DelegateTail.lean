import Examples.Ballot.DelegateLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## Parameterized `delegate(address)` post-loop tail helpers -/

/-- Sender packed-slot value after setting `sender.voted = true` and
`sender.delegate = w`, where `w` is the final word found by the delegation loop. -/
def delegateTailSenderPackedStoreWord (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.lor ⟨1⟩
    (UInt256.lor
      (UInt256.mul (UInt256.land w solcAddrMask) ⟨256⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
        (delegateSenderPackedWord σ I)))

/-- Account map after the shared sender packed-slot write, parameterized by the
post-loop final delegate word. -/
def delegateTailAfterSenderMap (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (delegateSenderPackedSlot I)
    (delegateTailSenderPackedStoreWord σ I w)

def delegateTailUpdatedVoterWeight (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.add (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w)
    (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I)

def delegateTailFalseSuccessMap (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (delegateTailAfterSenderMap σ I w) (delegateVoterSlot w)
    (delegateTailUpdatedVoterWeight σ I w)

def delegateTailProposalsLengthWord (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  (delegateTailAfterSenderMap σ I w).find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD ⟨2⟩ ⟨0⟩)

def delegateTailProposalCountSlot (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256) +
    (UInt256.mul ⟨2⟩ (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w) +
      proposalsDataBase)

def delegateTailProposalCountWord (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  (delegateTailAfterSenderMap σ I w).find? I.codeOwner |>.option ⟨0⟩ (fun acc =>
    acc.storage.findD (delegateTailProposalCountSlot σ I w) ⟨0⟩)

def delegateTailUpdatedProposalCount (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.add (delegateTailProposalCountWord σ I w)
    (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I)

def delegateTailTrueSuccessMap (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (delegateTailAfterSenderMap σ I w)
    (delegateTailProposalCountSlot σ I w) (delegateTailUpdatedProposalCount σ I w)

def delegateTailVoterWeightCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterSlot w)

def delegateTailSenderPackedStoreCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.lor ⟨1⟩
    (UInt256.lor
      (UInt256.mul (UInt256.land w solcAddrMask) ⟨256⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
        (delegateSenderPackedCurrent evm I)))

def delegateTailAfterSenderState (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore (delegateAfterVotedState evm I) evm.executionEnv.codeOwner
    (delegateSenderPackedSlot I) (delegateTailSenderPackedStoreCurrent evm I w)

@[simp] theorem delegateTailAfterSenderState_executionEnv (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) :
    (delegateTailAfterSenderState evm I w).executionEnv = evm.executionEnv := by
  simp [delegateTailAfterSenderState]

def delegateTailVoterPackedCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterPackedSlot w)

def delegateTailVoterVotedByteCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  UInt256.land ⟨255⟩ (delegateTailVoterPackedCurrent evm w)

def delegateTailVoterVoteCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterVoteSlot w)

def delegateTailUpdatedVoterWeightCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.add (delegateTailVoterWeightCurrent (delegateTailAfterSenderState evm I w) w)
    (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)

def delegateTailFalseSuccessState (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore (delegateTailAfterSenderState evm I w)
    (delegateTailAfterSenderState evm I w).executionEnv.codeOwner (delegateVoterSlot w)
    (delegateTailUpdatedVoterWeightCurrent evm I w)

def delegateTailProposalsLengthCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def delegateTailProposalCountSlotCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256) +
    (UInt256.mul ⟨2⟩ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w) +
      proposalsDataBase)

def delegateTailProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
    (delegateTailAfterSenderState evm I w).executionEnv.codeOwner
    (delegateTailProposalCountSlotCurrent evm I w)

def delegateTailProposalCountEvaledRef (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int
      (Int.ofNat (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)),
      .field "voteCount"] }

def delegateTailUpdatedProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : UInt256 :=
  UInt256.add (delegateTailProposalCountCurrent evm I w)
    (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)

def delegateTailTrueSuccessState (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore (delegateTailAfterSenderState evm I w)
    (delegateTailAfterSenderState evm I w).executionEnv.codeOwner
    (delegateTailProposalCountSlotCurrent evm I w)
    (delegateTailUpdatedProposalCountCurrent evm I w)

@[simp] theorem delegateTailSenderPackedStoreWord_to_initial (σ : AccountMap)
    (I : ExecutionEnv) :
    delegateTailSenderPackedStoreWord σ I (delegateToWord I) =
      delegateSenderPackedStoreWord σ I := by
  rfl

@[simp] theorem delegateTailAfterSenderMap_to_initial (σ : AccountMap) (I : ExecutionEnv) :
    delegateTailAfterSenderMap σ I (delegateToWord I) = delegateAfterSenderMap σ I := by
  rfl

@[simp] theorem delegateTailSenderPackedStoreCurrent_to_initial (evm : EVM.State)
    (I : ExecutionEnv) :
    delegateTailSenderPackedStoreCurrent evm I (delegateToWord I) =
      delegateSenderPackedStoreCurrent evm I := by
  rfl

@[simp] theorem delegateTailAfterSenderState_to_initial (evm : EVM.State)
    (I : ExecutionEnv) :
    delegateTailAfterSenderState evm I (delegateToWord I) =
      delegateAfterSenderState evm I := by
  rfl

theorem delegateTailVoterWeightCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (w : UInt256) :
    delegateTailVoterWeightCurrent (initState cA gh bl σ σ₀ g A I) w =
      delegateVoterWeightWord σ I w := by
  rfl

theorem evalStorageRef_delegate_tail_voter (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (voterRef (.var "to")) = .ok (delegateCurrentVoterRef w) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterRef,
    evalExpr_delegate_current_to evm I w, delegateCurrentToValue, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateCurrentVoterRef]

theorem resolveStorageRef_delegate_tail_voter (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    resolveStorageRef? ballotConfig
        { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
        evm (voterRef (.var "to")) =
      .ok (delegateCurrentVoterRef w, voterStructTy) := by
  exact resolveStorageRef?_ok
    (hbase := by simp [delegateCurrentWithSenderStore, delegateCurrentStore, voterRef])
    (her := evalStorageRef_delegate_tail_voter evm I w)
    (hty := by
      simp [delegateCurrentVoterRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy])

theorem resolveStorageRef_delegate_tail_delegateField (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig
        { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
        evm (aliasF "delegate_" field) =
      .ok (delegateCurrentVoterFieldRef w field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateCurrentWithDelegateStore I w).get? "delegate_" =
        some (.storageRef (delegateCurrentVoterRef w) voterStructTy) := by
    simp [delegateCurrentWithDelegateStore]
  change
    (match (delegateCurrentWithDelegateStore I w).get? "delegate_" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w } evm
            (aliasF "delegate_" field) with
        | .ok er => do
            let ty' <- EvalResult.ofOption EvalError.storageError
              (storageTypeAt? ballotContract.storage er)
            pure (er, ty')
        | .revert => .revert
        | .error e => .error e) = .ok (delegateCurrentVoterFieldRef w field, ty)
  rw [hget]
  simp [evalStorageRefFrom?, evalStorageRefStep, delegateCurrentVoterRef,
    delegateCurrentVoterFieldRef, EvalResult.bind, EvalResult.ofOption, bind, pure, hty]

theorem resolveStorageRef_delegate_tail_senderField_afterDelegate (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig
        { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
        evm (aliasF "sender" field) = .ok (delegateSenderFieldRef I field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateCurrentWithDelegateStore I w).get? "sender" =
        some (.storageRef (delegateSenderRef I) voterStructTy) := by
    unfold delegateCurrentWithDelegateStore delegateCurrentWithSenderStore
    rw [store_get_ne ((delegateCurrentStore w).insert "sender"
      (.storageRef (delegateSenderRef I) voterStructTy))
      (.storageRef (delegateCurrentVoterRef w) voterStructTy) (by decide)]
    exact store_get_self (delegateCurrentStore w) "sender"
      (.storageRef (delegateSenderRef I) voterStructTy)
  change
    (match (delegateCurrentWithDelegateStore I w).get? "sender" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w } evm
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

theorem evalExpr_delegate_tail_to_afterDelegate (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.var "to") = .ok (delegateCurrentToValue w) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((delegateCurrentWithDelegateStore I w).get? "to") = .ok (delegateCurrentToValue w)
  rw [delegateCurrentWithDelegateStore_to]
  rfl

theorem delegateAssignTailVoted (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm .storage (aliasF "sender" "voted") (.bool true) =
        .ok ({ contract := ballotContract, locals := delegateCurrentWithDelegateStore I w },
          delegateAfterVotedState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_senderField_afterDelegate evm I w "voted"
    (.elem .bool) (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rw [voteStorageLocStore_bool_true_offset0]
  simp [delegateAfterVotedState, delegateSenderVotedStoreCurrent, delegateSenderPackedCurrent,
    delegateSenderPackedSlot, delegateSenderSlot]

theorem delegateAssignTailDelegate (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hacc : evm.lookupAccount evm.executionEnv.codeOwner ≠ none)
    (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateAfterVotedState evm I) .storage (aliasF "sender" "delegate")
      (delegateCurrentToValue w) =
        .ok ({ contract := ballotContract, locals := delegateCurrentWithDelegateStore I w },
          delegateTailAfterSenderState evm I w) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_senderField_afterDelegate (delegateAfterVotedState evm I)
    I w "delegate" (.elem .address) (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rcases hlookup : evm.lookupAccount evm.executionEnv.codeOwner with _ | acc
  · exact False.elim (hacc hlookup)
  unfold delegateTailAfterSenderState delegateAfterVotedState delegateTailSenderPackedStoreCurrent
    delegateSenderVotedStoreCurrent delegateSenderPackedCurrent delegateCurrentToValue
  unfold delegateSenderPackedSlot delegateSenderSlot
  rw [ballotStorageLocStore_address_offset1_after_bool_true (acc := acc) (hacc := hlookup)
    (hcanon := hcanon)]

theorem evalExpr_delegate_tail_delegate_weight (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.storage (aliasF "delegate_" "weight")) =
        .ok (.int (Int.ofNat (delegateTailVoterWeightCurrent evm w).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField evm I w "weight"
    (.elem (.int uint256Int)) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "weight")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateTailVoterWeightCurrent evm w).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateTailVoterWeightCurrent, delegateVoterSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_tail_delegate_weight_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hweight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) =
        .ok (.bool true) := by
  have hnat : 1 ≤ (delegateTailVoterWeightCurrent evm w).toNat := by
    have hnz : (delegateTailVoterWeightCurrent evm w).toNat ≠ 0 := by
      intro hz
      apply hweight
      apply u256_inj
      exact hz
    omega
  have hstorage := evalExpr_delegate_tail_delegate_weight evm I w
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hnat]

theorem evalExpr_delegate_tail_delegate_weight_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hweight : delegateTailVoterWeightCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) =
        .ok (.bool false) := by
  have hstorage := evalExpr_delegate_tail_delegate_weight evm I w
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hweight]

theorem evalExpr_delegate_tail_delegate_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hzero : delegateTailVoterVotedByteCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.storage (aliasF "delegate_" "voted")) = .ok (.bool false) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField evm I w "voted" (.elem .bool)
    (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "voted") (.elem .bool) =
        .ok (.bool false) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot w, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool false)
    rw [delegateStorageLocLoad_bool_offset0_false]
    simpa [delegateTailVoterVotedByteCurrent, delegateTailVoterPackedCurrent, u256_land_comm]
      using hzero
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_tail_delegate_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hnz : delegateTailVoterVotedByteCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.storage (aliasF "delegate_" "voted")) = .ok (.bool true) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField evm I w "voted" (.elem .bool)
    (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "voted") (.elem .bool) =
        .ok (.bool true) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot w, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool true)
    rw [delegateStorageLocLoad_bool_offset0_true]
    simpa [delegateTailVoterVotedByteCurrent, delegateTailVoterPackedCurrent, u256_land_comm]
      using hnz
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_tail_sender_weight_afterDelegate (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.storage (aliasF "sender" "weight")) =
        .ok (.int (Int.ofNat (delegateSenderWeightCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_senderField_afterDelegate evm I w "weight"
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

theorem evalExpr_delegate_tail_delegate_weight_add (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hfit :
      (delegateTailVoterWeightCurrent evm w).toNat +
          (delegateSenderWeightCurrent evm I).toNat < UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add (delegateTailVoterWeightCurrent evm w)
          (delegateSenderWeightCurrent evm I)).toNat)) := by
  have hdel := evalExpr_delegate_tail_delegate_weight evm I w
  have hsender := evalExpr_delegate_tail_sender_weight_afterDelegate evm I w
  have hlt : ¬ Int.ofNat ((delegateTailVoterWeightCurrent evm w).toNat +
      (delegateSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat ((delegateTailVoterWeightCurrent evm w).toNat +
      (delegateSenderWeightCurrent evm I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat (delegateTailVoterWeightCurrent evm w).toNat +
          Int.ofNat (delegateSenderWeightCurrent evm I).toNat =
        Int.ofNat ((delegateTailVoterWeightCurrent evm w).toNat +
          (delegateSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  have hword :
      (UInt256.add (delegateTailVoterWeightCurrent evm w)
          (delegateSenderWeightCurrent evm I)).toNat =
        (delegateTailVoterWeightCurrent evm w).toNat +
          (delegateSenderWeightCurrent evm I).toNat := by
    change ((delegateTailVoterWeightCurrent evm w) + (delegateSenderWeightCurrent evm I)).toNat = _
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

theorem evalExpr_delegate_tail_delegate_weight_add_revert (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hover : UInt256.size ≤
      (delegateTailVoterWeightCurrent evm w).toNat +
        (delegateSenderWeightCurrent evm I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hdel := evalExpr_delegate_tail_delegate_weight evm I w
  have hsender := evalExpr_delegate_tail_sender_weight_afterDelegate evm I w
  have hge : Int.ofNat ((delegateTailVoterWeightCurrent evm w).toNat +
      (delegateSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hadd :
      Int.ofNat (delegateTailVoterWeightCurrent evm w).toNat +
          Int.ofNat (delegateSenderWeightCurrent evm I).toNat =
        Int.ofNat ((delegateTailVoterWeightCurrent evm w).toNat +
          (delegateSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  simp [u256, evalExpr?, EvalResult.bind, bind, hdel, hsender, evalBinaryOp?, uint256Int,
    hadd]
  intro _
  exact_mod_cast hover

theorem delegateAssignTailVoterWeight (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w) .storage (aliasF "delegate_" "weight")
      (.int (Int.ofNat (delegateTailUpdatedVoterWeightCurrent evm I w).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateCurrentWithDelegateStore I w },
          delegateTailFalseSuccessState evm I w) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_delegateField (delegateTailAfterSenderState evm I w)
    I w "weight" (.elem (.int uint256Int)) (by rfl), bind, EvalResult.bind,
    EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateCurrentVoterFieldRef, delegateVoterSlot]
  rw [voteStorageLocStore_uint256]
  simp [delegateTailFalseSuccessState, delegateTailUpdatedVoterWeightCurrent, delegateVoterSlot]

theorem evalExpr_delegate_tail_delegate_vote (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      evm (.storage (aliasF "delegate_" "vote")) =
        .ok (.int (Int.ofNat (delegateTailVoterVoteCurrent evm w).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField evm I w "vote"
    (.elem (.int uint256Int)) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "vote")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateTailVoterVoteCurrent evm w).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateTailVoterVoteCurrent, delegateVoterVoteSlot, delegateVoterSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem delegateTailProposalCountSlotCurrent_spec (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    delegateTailProposalCountSlotCurrent evm I w =
      proposalElemSlot
          (.int (Int.ofNat
            (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)) +
        ⟨1⟩ := by
  unfold delegateTailProposalCountSlotCurrent proposalElemSlot
  rw [ballotKeyValueToWord_int_ofNat_toNat,
    voteU256_mul_comm ⟨2⟩
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w),
    u256_mul_two_ofNat]
  rw [u256_add_comm (UInt256.ofNat
    ((delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat * 2))
    proposalsDataBase]
  exact u256_add_comm _ _

theorem delegateTailArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    arrayIndexInBounds? ballotConfig (delegateTailAfterSenderState evm I w) ballotContract.storage
      "proposals" []
      (.int (Int.ofNat
        (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)) =
        .ok () := by
  have hboundStorage :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        UInt256.toNat (Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
          evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [delegateTailProposalsLengthCurrent] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hboundStorage]

theorem delegateTailArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    arrayIndexInBounds? ballotConfig (delegateTailAfterSenderState evm I w) ballotContract.storage
      "proposals" []
      (.int (Int.ofNat
        (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)) =
        .revert := by
  have hboundStorage :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        UInt256.toNat (Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
          evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [delegateTailProposalsLengthCurrent] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
          evm.executionEnv.codeOwner ⟨2⟩) ≤
        (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hleStorage]

theorem evalStorageRef_delegate_tail_proposalCount (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") =
        .ok (delegateTailProposalCountEvaledRef evm I w) := by
  have hvote := evalExpr_delegate_tail_delegate_vote (delegateTailAfterSenderState evm I w) I w
  have hboundsOk :
      arrayIndexInBounds? ballotConfig (delegateTailAfterSenderState evm I w) ballotContract.storage
        "proposals" []
        (.int (Int.ofNat
          (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)) =
          .ok () :=
    delegateTailArrayIndexInBounds_ok evm I w hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hvote, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsOk]
  simp [delegateTailProposalCountEvaledRef]

theorem evalStorageRef_delegate_tail_proposalCount_revert (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") = .revert := by
  have hvote := evalExpr_delegate_tail_delegate_vote (delegateTailAfterSenderState evm I w) I w
  have hboundsRevert :
      arrayIndexInBounds? ballotConfig (delegateTailAfterSenderState evm I w) ballotContract.storage
        "proposals" []
        (.int (Int.ofNat
          (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat)) =
          .revert :=
    delegateTailArrayIndexInBounds_revert evm I w hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hvote, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsRevert]

theorem evalExpr_delegate_tail_proposal_count (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")) =
        .ok (.int (Int.ofNat
          (delegateTailProposalCountCurrent evm I w).toNat)) := by
  have hbase :
      (delegateCurrentWithDelegateStore I w).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simp [delegateCurrentWithDelegateStore, delegateCurrentWithSenderStore, delegateCurrentStore,
      proposalF]
  have hty :
      storageTypeAt? ballotContract.storage (delegateTailProposalCountEvaledRef evm I w) =
        some (.elem (.int uint256Int)) := by
    simp [delegateTailProposalCountEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
      ballotStorageDecls, proposalStructTy, uint256St]
  have hloc :
      ballotConfig.storage.layout (delegateTailProposalCountEvaledRef evm I w) =
        fun _ => some (wordLoc (delegateTailProposalCountSlotCurrent evm I w)) := by
    funext evm'
    simp [delegateTailProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
      delegateTailProposalCountSlotCurrent_spec, u256_add_comm]
  have hload :
      storageLocLoad (delegateTailAfterSenderState evm I w)
          (wordLoc (delegateTailProposalCountSlotCurrent evm I w)) =
        .int (Int.ofNat
          (delegateTailProposalCountCurrent evm I w).toNat) := by
    change storageLocLoad (delegateTailAfterSenderState evm I w)
        (wordLoc (delegateTailProposalCountSlotCurrent evm I w)) =
      .int (Int.ofNat (Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
        (delegateTailAfterSenderState evm I w).executionEnv.codeOwner
        (delegateTailProposalCountSlotCurrent evm I w)).toNat)
    exact ballotStorageLocLoad_uint256 (delegateTailAfterSenderState evm I w)
      (delegateTailProposalCountSlotCurrent evm I w)
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_delegate_tail_proposalCount evm I w hbound)
    (hty := hty) (hloc := hloc)]
  rw [hload]

theorem evalExpr_delegate_tail_proposal_count_add (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hfit :
      (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add
          (delegateTailProposalCountCurrent evm I w)
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)).toNat)) := by
  have hcount := evalExpr_delegate_tail_proposal_count evm I w hbound
  have hweight :=
    evalExpr_delegate_tail_sender_weight_afterDelegate (delegateTailAfterSenderState evm I w) I w
  have hlt : ¬ Int.ofNat
      ((delegateTailProposalCountCurrent evm I w).toNat +
      (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) ≥
        (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat
      ((delegateTailProposalCountCurrent evm I w).toNat +
      (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat (delegateTailProposalCountCurrent evm I w).toNat +
          Int.ofNat (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat =
        Int.ofNat ((delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) := by
    exact (Int.natCast_add _ _).symm
  have hword :
      (UInt256.add (delegateTailProposalCountCurrent evm I w)
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)).toNat =
        (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat := by
    change ((delegateTailProposalCountCurrent evm I w) +
        (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)).toNat = _
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

theorem evalExpr_delegate_tail_proposal_count_add_revert (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hover : UInt256.size ≤
      (delegateTailProposalCountCurrent evm I w).toNat +
        (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hcount := evalExpr_delegate_tail_proposal_count evm I w hbound
  have hweight :=
    evalExpr_delegate_tail_sender_weight_afterDelegate (delegateTailAfterSenderState evm I w) I w
  have hge : Int.ofNat
      ((delegateTailProposalCountCurrent evm I w).toNat +
      (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) ≥
        (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hadd :
      Int.ofNat (delegateTailProposalCountCurrent evm I w).toNat +
          Int.ofNat (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat =
        Int.ofNat ((delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) := by
    exact (Int.natCast_add _ _).symm
  simp [u256, evalExpr?, EvalResult.bind, bind, hcount, hweight, evalBinaryOp?, uint256Int,
    hadd]
  intro _
  exact_mod_cast hover

theorem evalExpr_delegate_tail_proposal_count_add_oob_revert (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hrevert := evalStorageRef_delegate_tail_proposalCount_revert evm I w hbound
  have hbase :
      (delegateCurrentWithDelegateStore I w).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simp [delegateCurrentWithDelegateStore, delegateCurrentWithSenderStore, delegateCurrentStore,
      proposalF]
  rw [u256, evalExpr?]
  simp only [evalExpr?, hbase, resolveStorageRef?, hrevert, EvalResult.bind, bind]

theorem delegateAssignTailProposalCount (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (_hfit :
      (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
      (delegateTailAfterSenderState evm I w) .storage
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")
      (.int (Int.ofNat (delegateTailUpdatedProposalCountCurrent evm I w).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateCurrentWithDelegateStore I w },
          delegateTailTrueSuccessState evm I w) := by
  apply assignStorageRef_storage_scalar (er := delegateTailProposalCountEvaledRef evm I w)
      (loc := wordLoc (delegateTailProposalCountSlotCurrent evm I w))
      (ty := .elem (.int uint256Int))
      (hbase := by
        simp [delegateCurrentWithDelegateStore, delegateCurrentWithSenderStore,
          delegateCurrentStore, proposalF])
      (her := evalStorageRef_delegate_tail_proposalCount evm I w hbound)
      (hty := by simp [storageTypeAt?, delegateTailProposalCountEvaledRef, ballotContract,
        ballotStorageDecls, proposalStructTy, uint256St, storageTypeStep?])
      (hloc := by
        funext evm'
        simp [delegateTailProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
          delegateTailProposalCountSlotCurrent_spec, u256_add_comm])
  rw [voteStorageLocStore_uint256]
  simp [delegateTailTrueSuccessState, delegateTailUpdatedProposalCountCurrent]

theorem ballotDelegateSolm_tailAfterLoopDelegateWeight (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hweight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩) :
    ExecBlock ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm
      [ .letStorage "delegate_" (voterRef (.var "to")),
        .require (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) ]
      (.ok { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w } evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w hweight))
    ExecBlock.nil

theorem ballotDelegateSolm_tailDelegateWeightRevert (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hweight : delegateTailVoterWeightCurrent evm w = ⟨0⟩) :
    ExecBlock ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm
      [ .letStorage "delegate_" (voterRef (.var "to")),
        .require (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) ]
      .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_delegate_tail_delegate_weight_ge_false evm I w hweight))

theorem ballotDelegateBodyReverts_tailDelegateWeight (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w = ⟨0⟩) :
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
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_delegate_tail_delegate_weight_ge_false evm I w hdelegateWeight))

theorem ballotDelegateBodyReturns_tailNotVoted (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w = ⟨0⟩)
    (hfit :
      (delegateTailVoterWeightCurrent (delegateTailAfterSenderState evm I w) w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body
      (.returned { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
        (delegateTailFalseSuccessState evm I w) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanonInit hnotself)) ?_
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w
      hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate (delegateAfterVotedState evm I) I w)
      (delegateAssignTailDelegate evm I w hacc hcanonTail)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteFalse
    (evalExpr_delegate_tail_delegate_voted_false (delegateTailAfterSenderState evm I w) I w
      hdelegateNotVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_delegate_weight_add (delegateTailAfterSenderState evm I w) I w
        hfit)
      (delegateAssignTailVoterWeight evm I w)) ExecBlock.nil

theorem ballotDelegateBodyReverts_tailNotVotedOverflow (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateTailVoterWeightCurrent (delegateTailAfterSenderState evm I w) w).toNat +
        (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) :
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
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanonInit hnotself)) ?_
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w
      hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate (delegateAfterVotedState evm I) I w)
      (delegateAssignTailDelegate evm I w hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse
    (evalExpr_delegate_tail_delegate_voted_false (delegateTailAfterSenderState evm I w) I w
      hdelegateNotVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_delegate_weight_add_revert (delegateTailAfterSenderState evm I w) I w
      hover))

theorem ballotDelegateBodyReturns_tailVoted (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w ≠ ⟨0⟩)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hfit :
      (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body
      (.returned { contract := ballotContract, locals := delegateCurrentWithDelegateStore I w }
        (delegateTailTrueSuccessState evm I w) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanonInit hnotself)) ?_
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w
      hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate (delegateAfterVotedState evm I) I w)
      (delegateAssignTailDelegate evm I w hacc hcanonTail)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true (delegateTailAfterSenderState evm I w) I w
      hdelegateVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_proposal_count_add evm I w hbound hfit)
      (delegateAssignTailProposalCount evm I w hbound hfit)) ExecBlock.nil

theorem ballotDelegateBodyReverts_tailVotedOob (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w ≠ ⟨0⟩)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
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
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanonInit hnotself)) ?_
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w
      hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate (delegateAfterVotedState evm I) I w)
      (delegateAssignTailDelegate evm I w hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true (delegateTailAfterSenderState evm I w) I w
      hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_proposal_count_add_oob_revert evm I w hbound))

theorem ballotDelegateBodyReverts_tailVotedOverflow (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByteCurrent evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I } evm
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w ≠ ⟨0⟩)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hover : UInt256.size ≤
      (delegateTailProposalCountCurrent evm I w).toNat +
        (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) :
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
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanonInit hnotself)) ?_
  refine ExecBlock.consNormal hwhile ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_tail_delegate_weight_ge_true evm I w
      hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted evm I w)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate (delegateAfterVotedState evm I) I w)
      (delegateAssignTailDelegate evm I w hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true (delegateTailAfterSenderState evm I w) I w
      hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_proposal_count_add_revert evm I w hbound hover))

theorem ballotDelegateX_tailAfterDelegateWeightFrom1134 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
      [delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1134⟩ := hreach
  have hslot := delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon
  have rd1160 := evm_run rd1134 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land w solcAddrMask)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact hslot) (by decide) (by evm_ov) ]
  have rd1162 := evm_run rd1160 with [dup1]
  obtain ⟨_, _, rd1163₀⟩ := rd1162.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1163⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
      [delegateVoterWeightWord σ I w, delegateVoterSlot w, ⟨1⟩, delegateSenderSlot I,
        w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterWeightWord, delegateVoterSlot, initState] using rd1163₀⟩
  have rd1167 := evm_run rd1163 with [swap1, swap2, gt, iszero]
  have hweightNat : 1 ≤ (delegateVoterWeightWord σ I w).toNat := by
    have hnz : (delegateVoterWeightWord σ I w).toNat ≠ 0 := by
      intro hzero
      apply hdelegateWeight
      apply u256_inj
      exact hzero
    omega
  have hgt : UInt256.gt (⟨1⟩ : UInt256) (delegateVoterWeightWord σ I w) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by
      change 1 ≤ (delegateVoterWeightWord σ I w).toNat
      exact hweightNat)
  have rd1167' := rd1167
  rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1167'
  exact ⟨_, _, evm_run rd1167' with [push2 ⟨1174⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_tailDelegateWeightRevertFrom1134 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hdelegateWeight : delegateVoterWeightWord σ I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1134⟩ := hreach
  have hslot := delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon
  have rd1160 := evm_run rd1134 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land w solcAddrMask)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact hslot) (by decide) (by evm_ov) ]
  have rd1162 := evm_run rd1160 with [dup1]
  obtain ⟨_, _, rd1163₀⟩ := rd1162.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1163⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
      [delegateVoterWeightWord σ I w, delegateVoterSlot w, ⟨1⟩, delegateSenderSlot I,
        w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterWeightWord, delegateVoterSlot, initState] using rd1163₀⟩
  have rd1167 := evm_run rd1163 with [swap1, swap2, gt, iszero]
  have hgt : UInt256.gt (⟨1⟩ : UInt256) (delegateVoterWeightWord σ I w) = ⟨1⟩ := by
    rw [hdelegateWeight]
    decide
  have rd1167' := rd1167
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1167'
  have rd1171 := evm_run rd1167' with [push2 ⟨1174⟩, jumpiNT (by decide)]
  exact rd1171.revertStub (by decide) (by decide) (by decide) (by evm_ov)

theorem ballotDelegateTailWeightRevertEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReverts_tailDelegateWeight
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
  exact (ballotDelegateX_tailDelegateWeightRevertFrom1134 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hcanonTail hdelegateWeight hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem delegateLoopKeyMem_extract64_eq_delegateHashMem (old senderWord : UInt256) :
    (delegateLoopKeyMem old senderWord).extract 64 (delegateLoopKeyMem old senderWord).size =
      (delegateHashMem senderWord).extract 64 (delegateHashMem senderWord).size := by
  have hloop := delegateLoopKeyMem_read64 old senderWord
  rw [readWithPadding_eq_extract _ 64 (by rw [delegateLoopKeyMem_size])] at hloop
  have hhash := delegateHashMem_read64 senderWord
  rw [readWithPadding_eq_extract _ 64 (by rw [delegateHashMem_size])] at hhash
  rw [delegateLoopKeyMem_size, delegateHashMem_size]
  exact hloop.trans hhash.symm

set_option maxHeartbeats 4000000 in
theorem delegateHashMem_extract32_tail (senderWord : UInt256) :
    (delegateHashMem senderWord).extract 32 (delegateHashMem senderWord).size =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (delegateKeyMem senderWord).extract 64 (delegateKeyMem senderWord).size := by
  unfold delegateHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [delegateKeyMem_size]; omega)]
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hbaseFull]
  have hprefixSize :
      ((delegateKeyMem senderWord).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, delegateKeyMem_size]
    omega
  let B :=
    UInt256.toByteArray (⟨1⟩ : UInt256) ++
      (delegateKeyMem senderWord).extract (32 + 32) (delegateKeyMem senderWord).size
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window ((delegateKeyMem senderWord).extract 0 32)
    B
    32
    (((delegateKeyMem senderWord).extract 0 32) ++
      B).size
    (by rw [hprefixSize])]
  rw [hprefixSize]
  have hend :
      (((delegateKeyMem senderWord).extract 0 32 ++ B).size - 32) = B.size := by
    rw [ByteArray.size_append, hprefixSize]
    omega
  rw [hend]
  exact delegateByteArray_extract_all B

set_option maxHeartbeats 4000000 in
theorem delegateLoopHashMem_extract32_eq_delegateHashMem (old senderWord : UInt256) :
    (delegateLoopHashMem old senderWord).extract 32 (delegateLoopHashMem old senderWord).size =
      (delegateHashMem senderWord).extract 32 (delegateHashMem senderWord).size := by
  unfold delegateLoopHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [delegateLoopKeyMem_size]; omega)]
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hbaseFull]
  have hprefixSize : ((delegateLoopKeyMem old senderWord).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, delegateLoopKeyMem_size]
    omega
  let B :=
    UInt256.toByteArray (⟨1⟩ : UInt256) ++
      (delegateLoopKeyMem old senderWord).extract (32 + 32)
        (delegateLoopKeyMem old senderWord).size
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window ((delegateLoopKeyMem old senderWord).extract 0 32)
    B
    32
    (((delegateLoopKeyMem old senderWord).extract 0 32) ++
      B).size
    (by rw [hprefixSize])]
  rw [hprefixSize]
  have hend :
      (((delegateLoopKeyMem old senderWord).extract 0 32 ++ B).size - 32) = B.size := by
    rw [ByteArray.size_append, hprefixSize]
    omega
  rw [hend]
  rw [show 32 - 32 = 0 by omega]
  rw [delegateByteArray_extract_all B]
  dsimp [B]
  rw [delegateLoopKeyMem_extract64_eq_delegateHashMem old senderWord]
  have hhash64 :
      (delegateHashMem senderWord).extract 64 (delegateHashMem senderWord).size =
        (delegateKeyMem senderWord).extract 64 (delegateKeyMem senderWord).size := by
    have hhash := delegateHashMem_read64 senderWord
    rw [readWithPadding_eq_extract _ 64 (by rw [delegateHashMem_size])] at hhash
    have hkey := delegateKeyMem_read64 senderWord
    rw [readWithPadding_eq_extract _ 64 (by rw [delegateKeyMem_size])] at hkey
    rw [delegateHashMem_size, delegateKeyMem_size]
    exact hhash.trans hkey.symm
  rw [hhash64]
  exact (delegateHashMem_extract32_tail senderWord).symm

theorem delegateLoopHashMem_writeKey_of_old (old w senderWord : UInt256) :
    (UInt256.toByteArray w).write 0 (delegateLoopHashMem old senderWord) 0 32 =
      delegateLoopKeyMem w senderWord := by
  rw [write32_eq _ _ 0 (by rw [toByteArray_size])
      (by rw [delegateLoopHashMem_size]; omega)]
  have hempty : (delegateLoopHashMem old senderWord).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hwFull : (UInt256.toByteArray w).extract 0 32 = UInt256.toByteArray w := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray w).size ≤ 32
      rw [toByteArray_size])
  rw [hempty, ByteArray.empty_append, hwFull]
  rw [show 0 + 32 = 32 from rfl, delegateLoopHashMem_size]
  rw [show (delegateLoopHashMem old senderWord).extract 32 96 =
      (delegateLoopHashMem old senderWord).extract 32
        (delegateLoopHashMem old senderWord).size by rw [delegateLoopHashMem_size]]
  rw [delegateLoopHashMem_extract32_eq_delegateHashMem old senderWord]
  unfold delegateLoopKeyMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size])
      (by rw [delegateHashMem_size]; omega)]
  have hbaseEmpty : (delegateHashMem senderWord).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hbaseEmpty, ByteArray.empty_append, hwFull, show 0 + 32 = 32 from rfl]

theorem delegateCurrentLoopMem_writeKey (I : ExecutionEnv) (old w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    (UInt256.toByteArray (UInt256.land w solcAddrMask)).write 0
        (delegateCurrentLoopMem I old) 0 32 =
      delegateLoopKeyMem w (delegateSourceWord I) := by
  rw [solcAddrMask_clean hcanon]
  unfold delegateCurrentLoopMem
  exact delegateLoopHashMem_writeKey_of_old old w (delegateSourceWord I)

theorem delegateCurrentLoopMem_writeKey_leftMask (I : ExecutionEnv) (old w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
        (delegateCurrentLoopMem I old) 0 32 =
      delegateLoopKeyMem w (delegateSourceWord I) := by
  rw [u256_land_comm solcAddrMask w]
  exact delegateCurrentLoopMem_writeKey I old w hcanon

theorem delegateCurrentLoopMem_writeBase_afterKey (I : ExecutionEnv) (old w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
        ((UInt256.toByteArray (UInt256.land w solcAddrMask)).write 0
          (delegateCurrentLoopMem I old) 0 32)
        32 32 =
      delegateCurrentLoopMem I w := by
  rw [delegateCurrentLoopMem_writeKey I old w hcanon]
  unfold delegateCurrentLoopMem delegateLoopHashMem
  rfl

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopExitFrom972Current {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel old w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hdelegate : delegateVoterDelegateWord σ I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I old) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        exact delegateCurrentLoopMem_writeKey_leftMask I old w hcanon)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem delegateLoopHashMem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.delegateDiv rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨1⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨1⟩
    rw [hdelegate]
    decide
  have rd1008' := rd1008
  rw [hzero] at rd1008'
  exact ⟨_, _, evm_run rd1008' with [push2 ⟨1134⟩, jumpiT (by decide) (by jump_dest)]⟩

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopContinueFrom972Current {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel old w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hnotSender : delegateVoterDelegateWord σ I w ≠ delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I old) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, delegateVoterDelegateWord σ I w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        exact delegateCurrentLoopMem_writeKey_leftMask I old w hcanon)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem delegateLoopHashMem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.delegateDiv rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hnonzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨0⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨0⟩
    exact isZero_eq_zero_of_ne hnext
  have rd1008' := rd1008
  rw [hnonzero] at rd1008'
  have rd1013 := evm_run rd1008' with [push2 ⟨1134⟩, jumpiNT (by decide)]
  have rd1041 := evm_run rd1013 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1042₀⟩ := rd1041.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1042⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1042⟩
      [delegateVoterPackedWord σ I w, delegateSenderSlot I, solcAddrMask, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, initState, u256_add_comm]
        using rd1042₀⟩
  have rd1045 := evm_run rd1042 with [push2 ⟨256⟩, swap1]
  have rd1046 := RD.delegateDiv rd1045 (by native_decide) (by norm_num)
  have rd1054 := evm_run rd1046 with [swap1, swap2, and, swap1, caller, dup3, sub]
  have hdiff :
      UInt256.sub
          (UInt256.land solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩))
          (UInt256.ofNat I.source.val) ≠ ⟨0⟩ := by
    rw [u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
    change UInt256.sub (delegateVoterDelegateWord σ I w) (delegateSourceWord I) ≠ ⟨0⟩
    exact u256_sub_ne_zero_of_ne hnotSender
  have rd972next := evm_run rd1054 with [
    push2 ⟨1129⟩, jumpiT hdiff (by jump_dest),
    jumpdest, push2 ⟨972⟩, jump (by jump_dest) ]
  exact ⟨_, _, by
    simpa [delegateVoterDelegateWord,
      u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
      using rd972next⟩

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopSenderRevertTailFrom972Current {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel old w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I w = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I old) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ R k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1058⟩ R
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C ∧
      R.length + 4 ≤ 1024 := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        exact delegateCurrentLoopMem_writeKey_leftMask I old w hcanon)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem delegateLoopHashMem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.delegateDiv rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hnonzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨0⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨0⟩
    exact isZero_eq_zero_of_ne hnext
  have rd1008' := rd1008
  rw [hnonzero] at rd1008'
  have rd1013 := evm_run rd1008' with [push2 ⟨1134⟩, jumpiNT (by decide)]
  have rd1041 := evm_run rd1013 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1042₀⟩ := rd1041.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1042⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1042⟩
      [delegateVoterPackedWord σ I w, delegateSenderSlot I, solcAddrMask, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, initState, u256_add_comm]
        using rd1042₀⟩
  have rd1045 := evm_run rd1042 with [push2 ⟨256⟩, swap1]
  have rd1046 := RD.delegateDiv rd1045 (by native_decide) (by norm_num)
  have rd1054 := evm_run rd1046 with [swap1, swap2, and, swap1, caller, dup3, sub]
  have hdiff :
      UInt256.sub
          (UInt256.land solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩))
          (UInt256.ofNat I.source.val) = ⟨0⟩ := by
    rw [u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
    change UInt256.sub (delegateVoterDelegateWord σ I w) (delegateSourceWord I) = ⟨0⟩
    rw [hcycle]
    exact u256_sub_self (delegateSourceWord I)
  have rd1054' := rd1054
  rw [hdiff] at rd1054'
  have rd1058 := evm_run rd1054' with [push2 ⟨1129⟩, jumpiNT (by decide)]
  exact ⟨_, _, _, rd1058, by simp⟩

theorem ballotDelegateX_loopSenderRevertFrom972Current {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel old w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I w = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I old) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨R, k, C, rd1058, hov⟩ :=
    ballotDelegateX_loopSenderRevertTailFrom972Current (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (old := old) (w := w) hcanon hnext hcycle hreach
  exact ballotDelegateX_loopFoundRevert1058 (sel := sel) (w := w) rd1058 hov

theorem ballotDelegateX_tailAfterSenderPackedStoreFrom1134 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hperm : I.perm = true)
    (hcanon : w.toNat < EVM.addressModulus)
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1174⟩ :=
    ballotDelegateX_tailAfterDelegateWeightFrom1134 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (w := w)
      hcanon hdelegateWeight hreach
  have rd1181 := evm_run rd1174 with [jumpdest, push1 ⟨1⟩, dup3, dup2, add, dup1]
  obtain ⟨_, _, rd1182₀⟩ := rd1181.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1182⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1182⟩
      [delegateSenderPackedWord σ I, delegateSenderPackedSlot I, ⟨1⟩,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [delegateSenderPackedWord, delegateSenderPackedSlot, initState, u256_add_comm]
        using rd1182₀⟩
  have rd1205 := evm_run rd1182 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨168⟩, shl, sub, not, and,
    push2 ⟨256⟩, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and, mul ]
  have rd1207 := RD.delegateOr rd1205 (by decide) (by evm_ov)
  have rd1208 := evm_run rd1207 with [dup3]
  have rd1209 := RD.delegateOr rd1208 (by decide) (by evm_ov)
  have rd1210 := evm_run rd1209 with [swap1]
  obtain ⟨_, _, rd1211⟩ := rd1210.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [delegateTailAfterSenderMap, delegateTailSenderPackedStoreWord,
      delegateSenderPackedWord, delegateSenderPackedSlot, initState] using rd1211⟩

theorem ballotDelegateX_tailDelegateNotVotedBranchFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1285⟩
      [delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1211⟩ := hreach
  have rd1213 := evm_run rd1211 with [dup2, add]
  obtain ⟨_, _, rd1214₀⟩ := rd1213.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1214⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1214⟩
      [delegateVoterPackedWord (delegateTailAfterSenderMap σ I w) I w,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot] using rd1214₀⟩
  have rd1218 := evm_run rd1214 with [push1 ⟨255⟩, and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land ⟨255⟩ (delegateVoterPackedWord (delegateTailAfterSenderMap σ I w) I w)) =
        ⟨1⟩ := by
    change UInt256.isZero (delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w) =
      ⟨1⟩
    rw [hdelegateNotVoted]
    decide
  have rd1218' := rd1218
  rw [hzero] at rd1218'
  exact ⟨_, _, evm_run rd1218' with [push2 ⟨1285⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_tailDelegateVotedBranchFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1222⟩
      [delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1211⟩ := hreach
  have rd1213 := evm_run rd1211 with [dup2, add]
  obtain ⟨_, _, rd1214₀⟩ := rd1213.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1214⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1214⟩
      [delegateVoterPackedWord (delegateTailAfterSenderMap σ I w) I w,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot] using rd1214₀⟩
  have rd1218 := evm_run rd1214 with [push1 ⟨255⟩, and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land ⟨255⟩ (delegateVoterPackedWord (delegateTailAfterSenderMap σ I w) I w)) =
        ⟨0⟩ := by
    change UInt256.isZero (delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w) =
      ⟨0⟩
    exact isZero_eq_zero_of_ne hdelegateVoted
  have rd1218' := rd1218
  rw [hzero] at rd1218'
  exact ⟨_, _, evm_run rd1218' with [push2 ⟨1285⟩, jumpiNT (by decide)]⟩

theorem ballotDelegateX_tailNotVotedToCheckedAddFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1835⟩
      [delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I, ⟨1304⟩, ⟨0⟩,
        delegateVoterSlot w, delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1285⟩ := ballotDelegateX_tailDelegateNotVotedBranchFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateNotVoted hreach
  have rd1287 := evm_run rd1285 with [jumpdest, dup2]
  obtain ⟨_, _, rd1288₀⟩ := rd1287.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1288⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1288⟩
      [delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by simpa [delegateSenderWeightWord, initState] using rd1288₀⟩
  have rd1289 := evm_run rd1288 with [dup2]
  obtain ⟨_, _, rd1290₀⟩ := rd1289.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1290⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1290⟩
      [delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by simpa [delegateVoterWeightWord, initState] using rd1290₀⟩
  exact ⟨_, _, evm_run rd1290 with [
    dup3, swap1, push0, swap1, push2 ⟨1304⟩, swap1, dup5, swap1, push2 ⟨1835⟩,
    jump (by jump_dest) ]⟩

theorem ballotDelegateX_tailNotVotedAfterCheckedAddFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1304⟩
      [delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I +
          delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w,
        ⟨0⟩, delegateVoterSlot w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_tailNotVotedToCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateNotVoted hreach
  let target := delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w
  let addend := delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hsumNat : (addend + target).toNat = addend.toNat + target.toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by simpa [target, addend, Nat.add_comm] using hfit)
  have hgt : UInt256.gt target (addend + target) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsumNat]; omega)
  have rd1842' := rd1842
  rw [show delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w = target from rfl,
      show delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I = addend from rfl,
      hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1842'
  have rd1866 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiT (by decide) (by jump_dest)]
  have rd1304 := evm_run rd1866 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [target, addend] using rd1304⟩

theorem ballotDelegateX_tailNotVotedSuccessFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hperm : I.perm = true)
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, delegateTailFalseSuccessMap σ I w) ByteArray.empty := by
  obtain ⟨_, _, rd1304⟩ := ballotDelegateX_tailNotVotedAfterCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateNotVoted hfit hreach
  have rd1307 := evm_run rd1304 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1308⟩ := rd1307.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd1308 with [
    pop, pop, jumpdest, pop, pop, pop, jump (by jump_dest), jumpdest ]
  have hsum :
      delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I +
          delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w =
        delegateTailUpdatedVoterWeight σ I w := by
    unfold delegateTailUpdatedVoterWeight
    exact u256_add_comm _ _
  exact by
    simpa [delegateTailFalseSuccessMap, hsum] using
      rd156.stop (by decide) (by evm_ov)

theorem ballotDelegateX_tailNotVotedOverflowFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
        (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_tailNotVotedToCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateNotVoted hreach
  let target := delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w
  let addend := delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hgt : UInt256.gt target (addend + target) = ⟨1⟩ := by
    exact delegateOverflowGt target addend (by simpa [target, addend] using hover)
  have rd1842' := rd1842
  rw [show delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w = target from rfl,
      show delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I = addend from rfl,
      hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1842'
  have rd1847 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiNT (by decide)]
  exact RD.ballotPanic11Revert1847 rd1847
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotDelegateX_tailVotedBoundsCheckFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1234⟩
      [UInt256.lt (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w)
          (delegateTailProposalsLengthWord σ I w),
        delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w, ⟨2⟩,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1222⟩ := ballotDelegateX_tailDelegateVotedBranchFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hreach
  have rd1223 := evm_run rd1222 with [dup2]
  obtain ⟨_, _, rd1224₀⟩ := rd1223.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1224⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1224⟩
      [delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by simpa [delegateSenderWeightWord, initState] using rd1224₀⟩
  have rd1229 := evm_run rd1224 with [push1 ⟨2⟩, dup3, dup2, add]
  obtain ⟨_, _, rd1230₀⟩ := rd1229.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1230⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1230⟩
      [delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w, ⟨2⟩,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by
      simpa [delegateVoterVoteWord, delegateVoterVoteSlot, initState, u256_add_comm]
        using rd1230₀⟩
  have rd1231 := evm_run rd1230 with [dup2]
  obtain ⟨_, _, rd1232₀⟩ := rd1231.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1232⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1232⟩
      [delegateTailProposalsLengthWord σ I w,
        delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w, ⟨2⟩,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by simpa [delegateTailProposalsLengthWord, initState] using rd1232₀⟩
  exact ⟨_, _, evm_run rd1232 with [dup2, lt]⟩

theorem ballotDelegateX_tailVotedOobFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound : ¬
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1234⟩ := ballotDelegateX_tailVotedBoundsCheckFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hreach
  have hlt :
      UInt256.lt (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w)
        (delegateTailProposalsLengthWord σ I w) = ⟨0⟩ :=
    ult_zero (Nat.le_of_not_gt hbound)
  have rd1234' := rd1234
  rw [hlt] at rd1234'
  have rd1815 := evm_run rd1234' with [
    push2 ⟨1245⟩, jumpiNT (by decide), push2 ⟨1245⟩, push2 ⟨1815⟩,
    jump (by jump_dest) ]
  exact RD.ballotPanic32Revert1815 rd1815
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotDelegateX_tailVotedToCheckedAddFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1835⟩
      [delegateTailProposalCountWord σ I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I, ⟨1274⟩, ⟨0⟩,
        delegateTailProposalCountSlot σ I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateProposalBaseMem w (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1234⟩ := ballotDelegateX_tailVotedBoundsCheckFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hreach
  have hlt :
      UInt256.lt (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w)
        (delegateTailProposalsLengthWord σ I w) = ⟨1⟩ :=
    ult_one hbound
  have rd1234' := rd1234
  rw [hlt] at rd1234'
  have rd1245 := evm_run rd1234' with [push2 ⟨1245⟩, jumpiT (by decide) (by jump_dest)]
  have hbase := delegateProposalsDataBaseKeccak w (delegateSourceWord I)
  have rd1261 := evm_run rd1245 with [
    jumpdest, swap1, push0,
    raw mstore 0 (delegateProposalBaseMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
      mem_cost hbase (by decide) (by evm_ov),
    swap1, push1 ⟨2⟩, mul, add, push1 ⟨1⟩, add ]
  have rd1264 := evm_run rd1261 with [push0, dup3, dup3]
  obtain ⟨_, _, rd1265₀⟩ := rd1264.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1265⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1265⟩
      [delegateTailProposalCountWord σ I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I, ⟨0⟩,
        delegateTailProposalCountSlot σ I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateProposalBaseMem w (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateTailAfterSenderMap σ I w) k C := by
    exact ⟨_, _, by
      simpa [delegateTailProposalCountWord, delegateTailProposalCountSlot, initState]
        using rd1265₀⟩
  exact ⟨_, _, evm_run rd1265 with [
    push2 ⟨1274⟩, swap2, swap1, push2 ⟨1835⟩, jump (by jump_dest) ]⟩

theorem ballotDelegateX_tailVotedAfterCheckedAddFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hfit :
      (delegateTailProposalCountWord σ I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩
      [delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I +
          delegateTailProposalCountWord σ I w,
        ⟨0⟩, delegateTailProposalCountSlot σ I w,
        delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I,
        delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateProposalBaseMem w (delegateSourceWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, delegateTailAfterSenderMap σ I w) k C := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_tailVotedToCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hbound hreach
  let target := delegateTailProposalCountWord σ I w
  let addend := delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hsumNat : (addend + target).toNat = addend.toNat + target.toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by simpa [target, addend, Nat.add_comm] using hfit)
  have hgt : UInt256.gt target (addend + target) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsumNat]; omega)
  have rd1842' := rd1842
  rw [show delegateTailProposalCountWord σ I w = target from rfl,
      show delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I = addend from rfl,
      hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1842'
  have rd1866 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiT (by decide) (by jump_dest)]
  have rd1274 := evm_run rd1866 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [target, addend] using rd1274⟩

theorem ballotDelegateX_tailVotedSuccessFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hperm : I.perm = true)
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hfit :
      (delegateTailProposalCountWord σ I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, delegateTailTrueSuccessMap σ I w) ByteArray.empty := by
  obtain ⟨_, _, rd1274⟩ := ballotDelegateX_tailVotedAfterCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hbound hfit hreach
  have rd1277 := evm_run rd1274 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1278⟩ := rd1277.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd1278 with [
    pop, push2 ⟨1310⟩, swap1, pop, jump (by jump_dest), jumpdest, pop, pop, pop,
    jump (by jump_dest), jumpdest ]
  have hsum :
      delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I +
          delegateTailProposalCountWord σ I w =
        delegateTailUpdatedProposalCount σ I w := by
    unfold delegateTailUpdatedProposalCount
    exact u256_add_comm _ _
  exact by
    simpa [delegateTailTrueSuccessMap, hsum] using rd156.stop (by decide) (by evm_ov)

theorem ballotDelegateX_tailVotedOverflowFrom1211 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel w : UInt256}
    (hdelegateVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hover : UInt256.size ≤
      (delegateTailProposalCountWord σ I w).toNat +
        (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1211⟩
      [⟨1⟩, delegateVoterSlot w, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
      (cA, delegateTailAfterSenderMap σ I w) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1835⟩ := ballotDelegateX_tailVotedToCheckedAddFrom1211
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (w := w) hdelegateVoted hbound hreach
  let target := delegateTailProposalCountWord σ I w
  let addend := delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hgt : UInt256.gt target (addend + target) = ⟨1⟩ := by
    exact delegateOverflowGt target addend (by simpa [target, addend] using hover)
  have rd1842' := rd1842
  rw [show delegateTailProposalCountWord σ I w = target from rfl,
      show delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I = addend from rfl,
      hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1842'
  have rd1847 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiNT (by decide)]
  exact RD.ballotPanic11Revert1847 rd1847
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem delegateTailSenderPackedStoreWord_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) :
    delegateTailSenderPackedStoreWord σ I w ≠ ⟨0⟩ := by
  unfold delegateTailSenderPackedStoreWord
  exact u256_lor_one_ne_zero _

theorem delegateTailAfterSenderState_findD_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (w readSlot : UInt256) :
    (((delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w).accountMap.find?
          (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w).executionEnv.codeOwner).option
        (default : UInt256)
        (fun acc => acc.storage.findD readSlot default)) =
      (((delegateTailAfterSenderMap σ I w).find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot default)) := by
  have hfinal : (delegateTailSenderPackedStoreWord σ I w == (default : UInt256)) = false := by
    simpa using delegateTailSenderPackedStoreWord_ne_zero σ I w
  have hlookup := sstoreAccountMap_self_storage_findD_update_insert_self
    σ I.codeOwner (delegateSenderPackedSlot I) readSlot
    (delegateSenderVotedStoreCurrent (initState cA gh bl σ σ₀ g A I) I)
    (delegateTailSenderPackedStoreWord σ I w) hfinal
  simpa [delegateTailAfterSenderState, delegateAfterVotedState, delegateTailAfterSenderMap,
    delegateTailSenderPackedStoreCurrent, delegateTailSenderPackedStoreWord,
    delegateSenderVotedStoreCurrent, delegateSenderPackedCurrent, delegateSenderPackedWord,
    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    storageStore_accountMap, voteStorageStore_executionEnv] using hlookup

theorem delegateTailVoterVotedByteCurrent_afterSenderState_init
    {cA gh bl σ σ₀ A I} {g : Sat256} (w : UInt256) :
    delegateTailVoterVotedByteCurrent
        (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w) w =
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w := by
  simpa [delegateTailVoterVotedByteCurrent, delegateVoterVotedByte,
    delegateTailVoterPackedCurrent, delegateVoterPackedWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using congrArg (fun word => UInt256.land ⟨255⟩ word)
      (delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w
        (delegateVoterPackedSlot w))

theorem delegateTailVoterWeightCurrent_afterSenderState_init
    {cA gh bl σ σ₀ A I} {g : Sat256} (w : UInt256) :
    delegateTailVoterWeightCurrent
        (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w) w =
      delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w := by
  simpa [delegateTailVoterWeightCurrent, delegateVoterWeightWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w (delegateVoterSlot w)

theorem delegateTailSenderWeightCurrent_afterSenderState_init
    {cA gh bl σ σ₀ A I} {g : Sat256} (w : UInt256) :
    delegateSenderWeightCurrent
        (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w) I =
      delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I := by
  simpa [delegateSenderWeightCurrent, delegateSenderWeightWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w (delegateSenderSlot I)

theorem delegateTailVoterVoteCurrent_afterSenderState_init
    {cA gh bl σ σ₀ A I} {g : Sat256} (w : UInt256) :
    delegateTailVoterVoteCurrent
        (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w) w =
      delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w := by
  simpa [delegateTailVoterVoteCurrent, delegateVoterVoteWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
    using delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w (delegateVoterVoteSlot w)

theorem delegateTailProposalsLengthCurrent_afterSenderState_init
    {cA gh bl σ σ₀ A I} {g : Sat256} (w : UInt256) :
    delegateTailProposalsLengthCurrent
        (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w) =
      delegateTailProposalsLengthWord σ I w := by
  simpa [delegateTailProposalsLengthCurrent, delegateTailProposalsLengthWord,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    using delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w ⟨2⟩

theorem delegateTailProposalCountCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (w : UInt256) :
    delegateTailProposalCountCurrent (initState cA gh bl σ σ₀ g A I) I w =
      delegateTailProposalCountWord σ I w := by
  unfold delegateTailProposalCountCurrent delegateTailProposalCountSlotCurrent
  rw [delegateTailVoterVoteCurrent_afterSenderState_init]
  simpa [delegateTailProposalCountWord, delegateTailProposalCountSlot, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, initState, voteStorageStore_executionEnv]
    using delegateTailAfterSenderState_findD_init (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) w
      (delegateTailProposalCountSlot σ I w)

theorem delegateTailSenderWeightWord_afterSenderMap (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256) :
    delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I =
      delegateSenderWeightWord σ I := by
  unfold delegateSenderWeightWord delegateTailAfterSenderMap
  exact sstoreAccountMap_storage_findD_ne σ I.codeOwner (delegateSenderSlot I)
    (delegateSenderPackedSlot I) (delegateTailSenderPackedStoreWord σ I w)
    (delegateSenderSlot_ne_packedSlot I)

theorem delegateTailUpdatedVoterWeight_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size) :
    delegateTailUpdatedVoterWeight σ I w ≠ ⟨0⟩ := by
  unfold delegateTailUpdatedVoterWeight
  apply u256_add_ne_zero_of_right_ne_zero
  · simpa [delegateTailSenderWeightWord_afterSenderMap] using hweight
  · exact hfit

theorem delegateTailUpdatedProposalCount_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (w : UInt256)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateTailProposalCountWord σ I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size) :
    delegateTailUpdatedProposalCount σ I w ≠ ⟨0⟩ := by
  unfold delegateTailUpdatedProposalCount
  apply u256_add_ne_zero_of_right_ne_zero
  · simpa [delegateTailSenderWeightWord_afterSenderMap] using hweight
  · exact hfit

theorem delegateTailAfterSenderState_accountMapEquiv_init {cA gh bl σ σ₀ A I}
    {g : Sat256} (w : UInt256) :
    accountMapEquiv (delegateTailAfterSenderMap σ I w)
      (delegateTailAfterSenderState (initState cA gh bl σ σ₀ g A I) I w).accountMap := by
  have hfinal : (delegateTailSenderPackedStoreWord σ I w == (default : UInt256)) = false := by
    simpa using delegateTailSenderPackedStoreWord_ne_zero σ I w
  have h := accountMapEquiv_sstoreAccountMap_self_update_insert
    σ I.codeOwner (delegateSenderPackedSlot I)
    (delegateSenderVotedStoreCurrent (initState cA gh bl σ σ₀ g A I) I)
    (delegateTailSenderPackedStoreWord σ I w) hfinal
  simpa [delegateTailAfterSenderState, delegateAfterVotedState, delegateTailAfterSenderMap,
    delegateTailSenderPackedStoreCurrent, delegateTailSenderPackedStoreWord,
    delegateSenderVotedStoreCurrent, delegateSenderPackedCurrent, delegateSenderPackedWord,
    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    storageStore_accountMap, voteStorageStore_executionEnv] using h

theorem delegateTailFalseSuccessState_created_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (w : UInt256) :
    cA = (delegateTailFalseSuccessState (initState cA gh bl σ σ₀ g A I) I w).createdAccounts := by
  simp [delegateTailFalseSuccessState, delegateTailAfterSenderState, delegateAfterVotedState,
    initState, storageStore_createdAccounts]

theorem delegateTailFalseSuccessState_accountMapEquiv_init {cA gh bl σ σ₀ A I}
    {g : Sat256} (w : UInt256)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size) :
    accountMapEquiv (delegateTailFalseSuccessMap σ I w)
      (delegateTailFalseSuccessState (initState cA gh bl σ σ₀ g A I) I w).accountMap := by
  have hfinal : (delegateTailUpdatedVoterWeight σ I w == (default : UInt256)) = false := by
    simpa using delegateTailUpdatedVoterWeight_ne_zero σ I w hweight hfit
  have hbase := delegateTailAfterSenderState_accountMapEquiv_init
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) w
  have h := accountMapEquiv_sstoreAccountMap_insert I.codeOwner
    (delegateVoterSlot w) (delegateTailUpdatedVoterWeight σ I w) hbase hfinal
  simpa [delegateTailFalseSuccessState, delegateTailFalseSuccessMap,
    delegateTailUpdatedVoterWeightCurrent, delegateTailUpdatedVoterWeight,
    delegateTailVoterWeightCurrent_afterSenderState_init,
    delegateTailSenderWeightCurrent_afterSenderState_init, storageStore_accountMap,
    voteStorageStore_executionEnv] using h

theorem delegateTailTrueSuccessState_created_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (w : UInt256) :
    cA = (delegateTailTrueSuccessState (initState cA gh bl σ σ₀ g A I) I w).createdAccounts := by
  simp [delegateTailTrueSuccessState, delegateTailAfterSenderState, delegateAfterVotedState,
    initState, storageStore_createdAccounts]

theorem delegateTailTrueSuccessState_accountMapEquiv_init {cA gh bl σ σ₀ A I}
    {g : Sat256} (w : UInt256)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hfit :
      (delegateTailProposalCountWord σ I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size) :
    accountMapEquiv (delegateTailTrueSuccessMap σ I w)
      (delegateTailTrueSuccessState (initState cA gh bl σ σ₀ g A I) I w).accountMap := by
  have hfinal : (delegateTailUpdatedProposalCount σ I w == (default : UInt256)) = false := by
    simpa using delegateTailUpdatedProposalCount_ne_zero σ I w hweight hfit
  have hbase := delegateTailAfterSenderState_accountMapEquiv_init
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) w
  have h := accountMapEquiv_sstoreAccountMap_insert I.codeOwner
    (delegateTailProposalCountSlot σ I w) (delegateTailUpdatedProposalCount σ I w) hbase hfinal
  simpa [delegateTailTrueSuccessState, delegateTailTrueSuccessMap,
    delegateTailUpdatedProposalCountCurrent, delegateTailUpdatedProposalCount,
    delegateTailProposalCountCurrent_init, delegateTailSenderWeightCurrent_afterSenderState_init,
    delegateTailProposalCountSlot, delegateTailProposalCountSlotCurrent,
    delegateTailVoterVoteCurrent_afterSenderState_init, storageStore_accountMap,
    voteStorageStore_executionEnv] using h

theorem ballotDelegateTailNotVotedSuccessEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hdelegateNotVoted : delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hfit :
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReturns_tailNotVoted
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateNotVoted)
    (by
      rw [delegateTailVoterWeightCurrent_afterSenderState_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hfit)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight hreach
  exact (ballotDelegateX_tailNotVotedSuccessFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hperm hdelegateNotVoted hfit hreach1211)
    |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
      (delegateTailFalseSuccessState_created_init (g := Sat256.ofUInt256 g) w)
      (delegateTailFalseSuccessState_accountMapEquiv_init
        (g := Sat256.ofUInt256 g) w hweight hfit)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateTailNotVotedOverflowEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hdelegateNotVoted : delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩)
    (hover : UInt256.size ≤
      (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
        (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReverts_tailNotVotedOverflow
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateNotVoted)
    (by
      rw [delegateTailVoterWeightCurrent_afterSenderState_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hover)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight hreach
  exact (ballotDelegateX_tailNotVotedOverflowFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateNotVoted hover hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateTailVotedSuccessEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hfit :
      (delegateTailProposalCountWord σ I w).toNat +
          (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReturns_tailVoted
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateVoted)
    (by
      rw [delegateTailVoterVoteCurrent_afterSenderState_init,
        delegateTailProposalsLengthCurrent_afterSenderState_init]
      exact hbound)
    (by
      rw [delegateTailProposalCountCurrent_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hfit)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight hreach
  exact (ballotDelegateX_tailVotedSuccessFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hperm hdelegateVoted hbound hfit hreach1211)
    |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
      (delegateTailTrueSuccessState_created_init (g := Sat256.ofUInt256 g) w)
      (delegateTailTrueSuccessState_accountMapEquiv_init
        (g := Sat256.ofUInt256 g) w hweight hfit)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateTailVotedOobEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound : ¬
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReverts_tailVotedOob
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateVoted)
    (by
      rw [delegateTailVoterVoteCurrent_afterSenderState_init,
        delegateTailProposalsLengthCurrent_afterSenderState_init]
      exact hbound)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight hreach
  exact (ballotDelegateX_tailVotedOobFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateVoted hbound hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateTailVotedOverflowEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonInit : (delegateToWord I).toNat < EVM.addressModulus)
    (hcanonTail : w.toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hwhile :
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hdelegateWeight : delegateVoterWeightWord σ I w ≠ ⟨0⟩)
    (hdelegateVoted : delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w ≠ ⟨0⟩)
    (hbound :
      (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
        (delegateTailProposalsLengthWord σ I w).toNat)
    (hover : UInt256.size ≤
      (delegateTailProposalCountWord σ I w).toNat +
        (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReverts_tailVotedOverflow
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself
    hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateVoted)
    (by
      rw [delegateTailVoterVoteCurrent_afterSenderState_init,
        delegateTailProposalsLengthCurrent_afterSenderState_init]
      exact hbound)
    (by
      rw [delegateTailProposalCountCurrent_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hover)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight hreach
  exact (ballotDelegateX_tailVotedOverflowFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateVoted hbound hover hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

end Ballot
