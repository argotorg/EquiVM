import Examples.Ballot.DelegateChain

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## Source-side delegate tail over arbitrary loop locals -/

abbrev delegateTailGeneralStore (I : ExecutionEnv) (w : UInt256) (L : Store) : Store :=
  L.insert "delegate_" (.storageRef (delegateCurrentVoterRef w) voterStructTy)

theorem delegateTailGeneralStore_to (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) :
    (delegateTailGeneralStore I w L).get? "to" = some (delegateCurrentToValue w) := by
  rw [delegateTailGeneralStore, store_get_ne L
    (.storageRef (delegateCurrentVoterRef w) voterStructTy) (by decide)]
  exact hL.1

theorem delegateTailGeneralStore_sender (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) :
    (delegateTailGeneralStore I w L).get? "sender" =
      some (.storageRef (delegateSenderRef I) voterStructTy) := by
  rw [delegateTailGeneralStore, store_get_ne L
    (.storageRef (delegateCurrentVoterRef w) voterStructTy) (by decide)]
  exact hL.2.1

theorem delegateTailGeneralStore_delegate (I : ExecutionEnv) (w : UInt256) (L : Store) :
    (delegateTailGeneralStore I w L).get? "delegate_" =
      some (.storageRef (delegateCurrentVoterRef w) voterStructTy) := by
  exact store_get_self L "delegate_" (.storageRef (delegateCurrentVoterRef w) voterStructTy)

theorem delegateTailGeneralStore_proposals (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) :
    (delegateTailGeneralStore I w L).get? "proposals" = none := by
  rw [delegateTailGeneralStore, store_get_ne L
    (.storageRef (delegateCurrentVoterRef w) voterStructTy) (by decide)]
  exact hL.2.2.2

theorem evalStorageRef_delegate_tail_voter_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := L } evm
      (voterRef (.var "to")) = .ok (delegateCurrentVoterRef w) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterRef,
    evalExpr_delegate_loopLocals_to evm I w L hL, delegateCurrentToValue, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateCurrentVoterRef]

theorem resolveStorageRef_delegate_tail_voter_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := L } evm
      (voterRef (.var "to")) = .ok (delegateCurrentVoterRef w, voterStructTy) := by
  exact resolveStorageRef?_ok
    (hbase := by
      simpa [voterRef, delegateLoopLocals] using hL.2.2.1)
    (her := evalStorageRef_delegate_tail_voter_general evm I w L hL)
    (hty := by
      simp [delegateCurrentVoterRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy])

theorem resolveStorageRef_delegate_tail_delegateField_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig
        { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm
        (aliasF "delegate_" field) =
      .ok (delegateCurrentVoterFieldRef w field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateTailGeneralStore I w L).get? "delegate_" =
        some (.storageRef (delegateCurrentVoterRef w) voterStructTy) :=
    delegateTailGeneralStore_delegate I w L
  change
    (match (delegateTailGeneralStore I w L).get? "delegate_" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm
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

theorem resolveStorageRef_delegate_tail_senderField_afterDelegate_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig
        { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm
        (aliasF "sender" field) = .ok (delegateSenderFieldRef I field, ty) := by
  rw [resolveStorageRef?]
  have hget :
      (delegateTailGeneralStore I w L).get? "sender" =
        some (.storageRef (delegateSenderRef I) voterStructTy) :=
    delegateTailGeneralStore_sender I w L hL
  change
    (match (delegateTailGeneralStore I w L).get? "sender" with
    | some (.storageRef er ty') =>
        evalStorageRefFrom? ballotConfig
          { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm er ty'
          [StorageRefStep.field field]
    | _ =>
        match
          evalStorageRef ballotConfig
            { contract := ballotContract, locals := delegateTailGeneralStore I w L } evm
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

theorem evalExpr_delegate_tail_to_afterDelegate_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.var "to") = .ok (delegateCurrentToValue w) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((delegateTailGeneralStore I w L).get? "to") = .ok (delegateCurrentToValue w)
  rw [delegateTailGeneralStore_to I w L hL]
  rfl

theorem delegateAssignTailVoted_general (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm .storage (aliasF "sender" "voted") (.bool true) =
        .ok ({ contract := ballotContract, locals := delegateTailGeneralStore I w L },
          delegateAfterVotedState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_senderField_afterDelegate_general evm I w L hL
    "voted" (.elem .bool) (by rfl), bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rw [voteStorageLocStore_bool_true_offset0]
  simp [delegateAfterVotedState, delegateSenderVotedStoreCurrent, delegateSenderPackedCurrent,
    delegateSenderPackedSlot, delegateSenderSlot]

theorem delegateAssignTailDelegate_general (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hacc : evm.lookupAccount evm.executionEnv.codeOwner ≠ none)
    (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateAfterVotedState evm I) .storage (aliasF "sender" "delegate")
      (delegateCurrentToValue w) =
        .ok ({ contract := ballotContract, locals := delegateTailGeneralStore I w L },
          delegateTailAfterSenderState evm I w) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_senderField_afterDelegate_general
    (delegateAfterVotedState evm I) I w L hL "delegate" (.elem .address) (by rfl),
    bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateSenderFieldRef, delegateSenderPackedSlot,
    delegateSenderSlot]
  rcases hlookup : evm.lookupAccount evm.executionEnv.codeOwner with _ | acc
  · exact False.elim (hacc hlookup)
  unfold delegateTailAfterSenderState delegateAfterVotedState delegateTailSenderPackedStoreCurrent
    delegateSenderVotedStoreCurrent delegateSenderPackedCurrent delegateCurrentToValue
  unfold delegateSenderPackedSlot delegateSenderSlot
  rw [ballotStorageLocStore_address_offset1_after_bool_true (acc := acc) (hacc := hlookup)
    (hcanon := hcanon)]

theorem evalExpr_delegate_tail_delegate_weight_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.storage (aliasF "delegate_" "weight")) =
        .ok (.int (Int.ofNat (delegateTailVoterWeightCurrent evm w).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField_general evm I w L "weight"
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

theorem evalExpr_delegate_tail_delegate_weight_ge_true_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hweight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) =
        .ok (.bool true) := by
  have hnat : 1 ≤ (delegateTailVoterWeightCurrent evm w).toNat := by
    have hnz : (delegateTailVoterWeightCurrent evm w).toNat ≠ 0 := by
      intro hz
      apply hweight
      apply u256_inj
      exact hz
    omega
  have hstorage := evalExpr_delegate_tail_delegate_weight_general evm I w L
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hnat]

theorem evalExpr_delegate_tail_delegate_weight_ge_false_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hweight : delegateTailVoterWeightCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)) =
        .ok (.bool false) := by
  have hstorage := evalExpr_delegate_tail_delegate_weight_general evm I w L
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hstorage, hweight]

theorem evalExpr_delegate_tail_delegate_voted_false_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hzero : delegateTailVoterVotedByteCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.storage (aliasF "delegate_" "voted")) = .ok (.bool false) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField_general evm I w L "voted"
    (.elem .bool) (by rfl)
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

theorem evalExpr_delegate_tail_delegate_voted_true_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hnz : delegateTailVoterVotedByteCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.storage (aliasF "delegate_" "voted")) = .ok (.bool true) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField_general evm I w L "voted"
    (.elem .bool) (by rfl)
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

theorem evalExpr_delegate_tail_sender_weight_afterDelegate_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.storage (aliasF "sender" "weight")) =
        .ok (.int (Int.ofNat (delegateSenderWeightCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_senderField_afterDelegate_general evm I w L hL
    "weight" (.elem (.int uint256Int)) (by rfl)
  have hread :
      readStorage? ballotConfig evm (delegateSenderFieldRef I "weight")
          (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (delegateSenderWeightCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [delegateSenderWeightCurrent, delegateSenderSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_tail_delegate_weight_add_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hfit :
      (delegateTailVoterWeightCurrent evm w).toNat +
          (delegateSenderWeightCurrent evm I).toNat < UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add (delegateTailVoterWeightCurrent evm w)
          (delegateSenderWeightCurrent evm I)).toNat)) := by
  have hdel := evalExpr_delegate_tail_delegate_weight_general evm I w L
  have hsender := evalExpr_delegate_tail_sender_weight_afterDelegate_general evm I w L hL
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
    change ((delegateTailVoterWeightCurrent evm w) + (delegateSenderWeightCurrent evm I)).toNat =
      _
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

theorem evalExpr_delegate_tail_delegate_weight_add_revert_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
    (hover : UInt256.size ≤
      (delegateTailVoterWeightCurrent evm w).toNat +
        (delegateSenderWeightCurrent evm I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm
      (u256 (.binary .add (.storage (aliasF "delegate_" "weight"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hdel := evalExpr_delegate_tail_delegate_weight_general evm I w L
  have hsender := evalExpr_delegate_tail_sender_weight_afterDelegate_general evm I w L hL
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

theorem delegateAssignTailVoterWeight_general (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w) .storage (aliasF "delegate_" "weight")
      (.int (Int.ofNat (delegateTailUpdatedVoterWeightCurrent evm I w).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateTailGeneralStore I w L },
          delegateTailFalseSuccessState evm I w) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_delegate_tail_delegateField_general
    (delegateTailAfterSenderState evm I w) I w L "weight" (.elem (.int uint256Int)) (by rfl),
    bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, delegateCurrentVoterFieldRef, delegateVoterSlot]
  rw [voteStorageLocStore_uint256]
  simp [delegateTailFalseSuccessState, delegateTailUpdatedVoterWeightCurrent, delegateVoterSlot]

theorem evalExpr_delegate_tail_delegate_vote_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      evm (.storage (aliasF "delegate_" "vote")) =
        .ok (.int (Int.ofNat (delegateTailVoterVoteCurrent evm w).toNat)) := by
  have hresolve := resolveStorageRef_delegate_tail_delegateField_general evm I w L "vote"
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

theorem evalStorageRef_delegate_tail_proposalCount_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalStorageRef ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") =
        .ok (delegateTailProposalCountEvaledRef evm I w) := by
  have hvote :=
    evalExpr_delegate_tail_delegate_vote_general (delegateTailAfterSenderState evm I w) I w L
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

theorem evalStorageRef_delegate_tail_proposalCount_revert_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalStorageRef ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount") = .revert := by
  have hvote :=
    evalExpr_delegate_tail_delegate_vote_general (delegateTailAfterSenderState evm I w) I w L
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

theorem evalExpr_delegate_tail_proposal_count_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")) =
        .ok (.int (Int.ofNat (delegateTailProposalCountCurrent evm I w).toNat)) := by
  have hbase :
      (delegateTailGeneralStore I w L).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simpa [proposalF] using delegateTailGeneralStore_proposals I w L hL
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
        .int (Int.ofNat (delegateTailProposalCountCurrent evm I w).toNat) := by
    change storageLocLoad (delegateTailAfterSenderState evm I w)
        (wordLoc (delegateTailProposalCountSlotCurrent evm I w)) =
      .int (Int.ofNat (Solm.EVM.storageLoad (delegateTailAfterSenderState evm I w)
        (delegateTailAfterSenderState evm I w).executionEnv.codeOwner
        (delegateTailProposalCountSlotCurrent evm I w)).toNat)
    exact ballotStorageLocLoad_uint256 (delegateTailAfterSenderState evm I w)
      (delegateTailProposalCountSlotCurrent evm I w)
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_delegate_tail_proposalCount_general evm I w L hbound)
    (hty := hty) (hloc := hloc)]
  rw [hload]

theorem evalExpr_delegate_tail_proposal_count_add_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hfit :
      (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add
          (delegateTailProposalCountCurrent evm I w)
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I)).toNat)) := by
  have hcount := evalExpr_delegate_tail_proposal_count_general evm I w L hL hbound
  have hweight :=
    evalExpr_delegate_tail_sender_weight_afterDelegate_general
      (delegateTailAfterSenderState evm I w) I w L hL
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

theorem evalExpr_delegate_tail_proposal_count_add_revert_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (hover : UInt256.size ≤
      (delegateTailProposalCountCurrent evm I w).toNat +
        (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hcount := evalExpr_delegate_tail_proposal_count_general evm I w L hL hbound
  have hweight :=
    evalExpr_delegate_tail_sender_weight_afterDelegate_general
      (delegateTailAfterSenderState evm I w) I w L hL
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

theorem evalExpr_delegate_tail_proposal_count_add_oob_revert_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
    (hbound :
      ¬ (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w)
      (u256 (.binary .add
        (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hrevert := evalStorageRef_delegate_tail_proposalCount_revert_general evm I w L hbound
  have hbase :
      (delegateTailGeneralStore I w L).get?
          (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount").base = none := by
    simpa [proposalF] using delegateTailGeneralStore_proposals I w L hL
  rw [u256, evalExpr?]
  simp only [evalExpr?, hbase, resolveStorageRef?, hrevert, EvalResult.bind, bind]

theorem delegateAssignTailProposalCount_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hbound :
      (delegateTailVoterVoteCurrent (delegateTailAfterSenderState evm I w) w).toNat <
        (delegateTailProposalsLengthCurrent (delegateTailAfterSenderState evm I w)).toNat)
    (_hfit :
      (delegateTailProposalCountCurrent evm I w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateTailGeneralStore I w L }
      (delegateTailAfterSenderState evm I w) .storage
      (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")
      (.int (Int.ofNat (delegateTailUpdatedProposalCountCurrent evm I w).toNat)) =
        .ok ({ contract := ballotContract, locals := delegateTailGeneralStore I w L },
          delegateTailTrueSuccessState evm I w) := by
  apply assignStorageRef_storage_scalar (er := delegateTailProposalCountEvaledRef evm I w)
      (loc := wordLoc (delegateTailProposalCountSlotCurrent evm I w))
      (ty := .elem (.int uint256Int))
      (hbase := by
        simpa [proposalF] using delegateTailGeneralStore_proposals I w L hL)
      (her := evalStorageRef_delegate_tail_proposalCount_general evm I w L hbound)
      (hty := by simp [storageTypeAt?, delegateTailProposalCountEvaledRef, ballotContract,
        ballotStorageDecls, proposalStructTy, uint256St, storageTypeStep?])
      (hloc := by
        funext evm'
        simp [delegateTailProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
          delegateTailProposalCountSlotCurrent_spec, u256_add_comm])
  rw [voteStorageLocStore_uint256]
  simp [delegateTailTrueSuccessState, delegateTailUpdatedProposalCountCurrent]

theorem ballotDelegateBodyReverts_tailDelegateWeight_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
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
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_delegate_tail_delegate_weight_ge_false_general evm I w L hdelegateWeight))

theorem ballotDelegateBodyReturns_tailNotVoted_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
    (hdelegateWeight : delegateTailVoterWeightCurrent evm w ≠ ⟨0⟩)
    (hdelegateNotVoted :
      delegateTailVoterVotedByteCurrent (delegateTailAfterSenderState evm I w) w = ⟨0⟩)
    (hfit :
      (delegateTailVoterWeightCurrent (delegateTailAfterSenderState evm I w) w).toNat +
          (delegateSenderWeightCurrent (delegateTailAfterSenderState evm I w) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body
      (.returned { contract := ballotContract, locals := delegateTailGeneralStore I w L }
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
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_delegate_tail_delegate_weight_ge_true_general evm I w L hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate_general (delegateAfterVotedState evm I) I w L hL)
      (delegateAssignTailDelegate_general evm I w L hL hacc hcanonTail)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteFalse
    (evalExpr_delegate_tail_delegate_voted_false_general (delegateTailAfterSenderState evm I w)
      I w L hdelegateNotVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_delegate_weight_add_general
        (delegateTailAfterSenderState evm I w) I w L hL hfit)
      (delegateAssignTailVoterWeight_general evm I w L)) ExecBlock.nil

theorem ballotDelegateBodyReverts_tailNotVotedOverflow_general
    (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
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
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_delegate_tail_delegate_weight_ge_true_general evm I w L hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate_general (delegateAfterVotedState evm I) I w L hL)
      (delegateAssignTailDelegate_general evm I w L hL hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse
    (evalExpr_delegate_tail_delegate_voted_false_general (delegateTailAfterSenderState evm I w)
      I w L hdelegateNotVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_delegate_weight_add_revert_general
      (delegateTailAfterSenderState evm I w) I w L hL hover))

theorem ballotDelegateBodyReturns_tailVoted_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
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
      (.returned { contract := ballotContract, locals := delegateTailGeneralStore I w L }
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
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_delegate_tail_delegate_weight_ge_true_general evm I w L hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate_general (delegateAfterVotedState evm I) I w L hL)
      (delegateAssignTailDelegate_general evm I w L hL hacc hcanonTail)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true_general (delegateTailAfterSenderState evm I w)
      I w L hdelegateVoted) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_proposal_count_add_general evm I w L hL hbound hfit)
      (delegateAssignTailProposalCount_general evm I w L hL hbound hfit)) ExecBlock.nil

theorem ballotDelegateBodyReverts_tailVotedOob_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
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
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_delegate_tail_delegate_weight_ge_true_general evm I w L hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate_general (delegateAfterVotedState evm I) I w L hL)
      (delegateAssignTailDelegate_general evm I w L hL hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true_general (delegateTailAfterSenderState evm I w)
      I w L hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_proposal_count_add_oob_revert_general evm I w L hL hbound))

theorem ballotDelegateBodyReverts_tailVotedOverflow_general (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L)
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
        (.ok { contract := ballotContract, locals := L } evm))
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
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_tail_voter_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_delegate_tail_delegate_weight_ge_true_general evm I w L hdelegateWeight)) ?_
  have hacc := delegateSenderWeightCurrent_ne_zero_account evm I hweight
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (delegateAssignTailVoted_general evm I w L hL)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_delegate_tail_to_afterDelegate_general (delegateAfterVotedState evm I) I w L hL)
      (delegateAssignTailDelegate_general evm I w L hL hacc hcanonTail)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (evalExpr_delegate_tail_delegate_voted_true_general (delegateTailAfterSenderState evm I w)
      I w L hdelegateVoted) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_delegate_tail_proposal_count_add_revert_general evm I w L hL hbound hover))

end Ballot
