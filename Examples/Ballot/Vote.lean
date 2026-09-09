import Examples.Ballot.Common
import Examples.Ballot.Proposals
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## `vote(uint256)` -/

abbrev voteProposalWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev voteProposalValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (voteProposalWord I).toNat)

abbrev voteStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "proposal" (voteProposalValue I)

abbrev voteSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def voteSenderSlot (I : ExecutionEnv) : UInt256 :=
  voterBase (.address I.source)

def voteSenderPackedSlot (I : ExecutionEnv) : UInt256 :=
  voteSenderSlot I + ⟨1⟩

def voteSenderVoteSlot (I : ExecutionEnv) : UInt256 :=
  voteSenderSlot I + ⟨2⟩

def voteProposalCountSlot (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (voteProposalWord I) ⟨2⟩ + proposalsDataBase + ⟨1⟩

def voteSenderWeightWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (voteSenderSlot I) ⟨0⟩)

def voteSenderPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (voteSenderPackedSlot I) ⟨0⟩)

def voteSenderVotedByte (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (voteSenderPackedWord σ I) ⟨255⟩

def voteProposalsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def voteProposalCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (voteProposalCountSlot I) ⟨0⟩)

def voteProposalsLengthCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def voteSenderWeightCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (voteSenderSlot I)

def voteSenderPackedCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (voteSenderPackedSlot I)

def voteSenderVotedByteCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (voteSenderPackedCurrent evm I) ⟨255⟩

def voteProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (voteProposalCountSlot I)

def voteSenderVotedStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (UInt256.land (voteSenderPackedWord σ I) (UInt256.lnot ⟨255⟩)) ⟨1⟩

def voteSenderVotedStoreCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (UInt256.land (voteSenderPackedCurrent evm I) (UInt256.lnot ⟨255⟩)) ⟨1⟩

def voteAfterVotedState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (voteSenderPackedSlot I)
    (voteSenderVotedStoreCurrent evm I)

def voteAfterVoteState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (voteAfterVotedState evm I) (voteAfterVotedState evm I).executionEnv.codeOwner
    (voteSenderVoteSlot I) (voteProposalWord I)

def voteUpdatedProposalCountCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (voteProposalCountCurrent (voteAfterVoteState evm I) I)
    (voteSenderWeightCurrent (voteAfterVoteState evm I) I)

def voteFinalState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (voteAfterVoteState evm I) (voteAfterVoteState evm I).executionEnv.codeOwner
    (voteProposalCountSlot I) (voteUpdatedProposalCountCurrent evm I)

def voteAfterVotedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (voteSenderPackedSlot I) (voteSenderVotedStoreWord σ I)

def voteAfterVoteMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (voteAfterVotedMap σ I) (voteSenderVoteSlot I) (voteProposalWord I)

def voteUpdatedProposalCount (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.add (voteProposalCountWord (voteAfterVoteMap σ I) I)
    (voteSenderWeightWord (voteAfterVoteMap σ I) I)

def voteSuccessMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (voteAfterVoteMap σ I) (voteProposalCountSlot I)
    (voteUpdatedProposalCount σ I)

theorem voteSenderWeightWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteSenderWeightWord σ I = voteSenderWeightWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (voteSenderSlot I) ⟨0⟩

theorem voteSenderPackedWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteSenderPackedWord σ I = voteSenderPackedWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (voteSenderPackedSlot I) ⟨0⟩

theorem voteSenderVotedByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteSenderVotedByte σ I = voteSenderVotedByte τ I := by
  unfold voteSenderVotedByte
  rw [voteSenderPackedWord_accountMapEquiv hστ]

theorem voteProposalsLengthWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteProposalsLengthWord σ I = voteProposalsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem voteProposalCountWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteProposalCountWord σ I = voteProposalCountWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (voteProposalCountSlot I) ⟨0⟩

theorem voteSenderVotedStoreWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    voteSenderVotedStoreWord σ I = voteSenderVotedStoreWord τ I := by
  unfold voteSenderVotedStoreWord
  rw [voteSenderPackedWord_accountMapEquiv hστ]

theorem voteAfterVotedMap_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (voteAfterVotedMap σ I) (voteAfterVotedMap τ I) := by
  rw [voteAfterVotedMap, voteAfterVotedMap, voteSenderVotedStoreWord_accountMapEquiv hστ]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner (voteSenderPackedSlot I)
    (voteSenderVotedStoreWord τ I) hστ

theorem voteAfterVoteMap_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (voteAfterVoteMap σ I) (voteAfterVoteMap τ I) := by
  rw [voteAfterVoteMap, voteAfterVoteMap]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner (voteSenderVoteSlot I) (voteProposalWord I)
    (voteAfterVotedMap_accountMapEquiv hστ)

-- `voteUpdatedProposalCount_accountMapEquiv` / `voteSuccessMap_accountMapEquiv` were retired when
-- the success connect moved to the `EVMStateEquiv` chain (`voteFinalState_EVMStateEquiv`), which
-- carries the account-map agreement compositionally through the three `SSTORE`s.

def voteSenderEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "voters", steps := [.mindex (.address I.source), .field field] }

def voteSenderBaseEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "voters", steps := [.mindex (.address I.source)] }

def voteProposalCountEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int (Int.ofNat (voteProposalWord I).toNat)), .field "voteCount"] }

abbrev voteAliasStore (I : ExecutionEnv) : Store :=
  (voteStore I).insert "sender" (.storageRef (voteSenderBaseEvaledRef I) voterStructTy)

theorem voteSourceWord_toNat (I : ExecutionEnv) :
    (voteSourceWord I).toNat = I.source.val := by
  unfold voteSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem voteSenderSlot_eq_hash (I : ExecutionEnv) :
    voteSenderSlot I =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (voteSourceWord I) ++
        UInt256.toByteArray (⟨1⟩ : UInt256))) := by
  unfold voteSenderSlot voterBase mapSlot
  rw [show keyValueToWord (.address I.source) = voteSourceWord I by
    simpa [voteSourceWord] using keyValueToWord_address I.source]

theorem voteProposalCountSlot_spec (I : ExecutionEnv) :
    voteProposalCountSlot I =
      proposalElemSlot (.int (Int.ofNat (voteProposalWord I).toNat)) + ⟨1⟩ := by
  unfold voteProposalCountSlot proposalElemSlot
  rw [keyValueToWord_uint256, u256_mul_two_ofNat]
  rw [u256_add_comm (UInt256.ofNat ((voteProposalWord I).toNat * 2)) proposalsDataBase]

theorem ballotDecode_vote_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (voteTransition.params.map Param.name)
      (transitionSignature voteTransition).paramTypes I.calldata = some (voteStore I) := by
  show decodeCalldata ["proposal"] [uint256] I.calldata = some (voteStore I)
  simpa [voteStore, voteProposalValue, voteProposalWord, uint256, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "proposal") hsz36 hbig

theorem ballotDecode_vote_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldata (voteTransition.params.map Param.name)
      (transitionSignature voteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["proposal"] [uint256] I.calldata = none
  simpa [uint256] using decodeCalldata_uint256_none_short (cd := I.calldata)
    (x := "proposal") hshort

theorem ballotDecode_vote_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (voteTransition.params.map Param.name)
      (transitionSignature voteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["proposal"] [uint256] I.calldata = none
  simpa [uint256] using decodeCalldata_uint256_none_huge (cd := I.calldata)
    (x := "proposal") hbig

/-! ### Local storage/source helpers -/

theorem voteStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem voteStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem voteStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool false := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem voteStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool true := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem voteStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocStore evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
        (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  simpa [boolOffset0Loc] using storageLocStore_bool_true_offset0 evm slot

theorem evalStorageRef_vote_sender (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := voteStore I } evm
      (voterRef sender) = .ok (voteSenderBaseEvaledRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, voterRef, sender,
    evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [hsource]
  rfl

theorem resolveStorageRef_vote_sender (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := voteStore I } evm
      (voterRef sender) = .ok (voteSenderBaseEvaledRef I, voterStructTy) := by
  unfold resolveStorageRef?
  rw [show (voteStore I).get? (voterRef sender).base = none by simp [voteStore, voterRef]]
  rw [evalStorageRef_vote_sender evm I hsource]
  simp [storageTypeAt?, voteSenderBaseEvaledRef, ballotContract, ballotStorageDecls, voterStructTy,
    storageTypeStep?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem resolveStorageRef_vote_senderField (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) (ty : StorageType)
    (hty : storageTypeStep? voterStructTy (.field field) = some ty) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (aliasF "sender" field) = .ok (voteSenderEvaledRef I field, ty) := by
  simp [resolveStorageRef?, evalStorageRefFrom?, evalStorageRefStep, aliasF, voteAliasStore,
    voteSenderBaseEvaledRef, voteSenderEvaledRef, EvalResult.bind, EvalResult.ofOption, bind,
    pure, hty]

theorem resolveStorageRef_vote_senderWeight (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (aliasF "sender" "weight") =
        .ok (voteSenderEvaledRef I "weight", .elem (.int uint256Int)) := by
  exact resolveStorageRef_vote_senderField evm I "weight" (.elem (.int uint256Int))
    (by simp [storageTypeStep?, voterStructTy, uint256St])

theorem resolveStorageRef_vote_senderVoted (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (aliasF "sender" "voted") =
        .ok (voteSenderEvaledRef I "voted", .elem .bool) := by
  exact resolveStorageRef_vote_senderField evm I "voted" (.elem .bool)
    (by simp [storageTypeStep?, voterStructTy, boolSt])

theorem resolveStorageRef_vote_senderVote (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (aliasF "sender" "vote") =
        .ok (voteSenderEvaledRef I "vote", .elem (.int uint256Int)) := by
  exact resolveStorageRef_vote_senderField evm I "vote" (.elem (.int uint256Int))
    (by simp [storageTypeStep?, voterStructTy, uint256St])

theorem evalExpr_vote_sender_weight (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.storage (aliasF "sender" "weight")) =
        .ok (.int (Int.ofNat (voteSenderWeightCurrent evm I).toNat)) := by
  have hresolve := resolveStorageRef_vote_senderWeight evm I
  have hread :
      readStorage? ballotConfig evm (voteSenderEvaledRef I "weight") (.elem (.int uint256Int)) =
        .ok (.int (Int.ofNat (voteSenderWeightCurrent evm I).toNat)) := by
    rw [readStorage?_elem (hloc := by rfl)]
    rw [ballotStorageLocLoad_uint256]
    simp [voteSenderWeightCurrent, voteSenderSlot]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_vote_sender_weight_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hweight : voteSenderWeightCurrent evm I ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)) = .ok (.bool true) := by
  have hstorage := evalExpr_vote_sender_weight evm I
  have hnat : (voteSenderWeightCurrent evm I).toNat ≠ 0 := by
    intro hz
    apply hweight
    apply u256_inj
    exact hz
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hnat]

theorem evalExpr_vote_sender_weight_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hweight : voteSenderWeightCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)) = .ok (.bool false) := by
  have hstorage := evalExpr_vote_sender_weight evm I
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hweight]

theorem evalExpr_vote_sender_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : voteSenderVotedByteCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.storage (aliasF "sender" "voted")) = .ok (.bool false) := by
  have hresolve := resolveStorageRef_vote_senderVoted evm I
  have hread :
      readStorage? ballotConfig evm (voteSenderEvaledRef I "voted") (.elem .bool) =
        .ok (.bool false) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := voteSenderPackedSlot I, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool false)
    rw [voteStorageLocLoad_bool_offset0_false evm (voteSenderPackedSlot I)]
    simpa [voteSenderVotedByteCurrent, voteSenderPackedCurrent] using hvoted
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_vote_sender_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : voteSenderVotedByteCurrent evm I ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.storage (aliasF "sender" "voted")) = .ok (.bool true) := by
  have hresolve := resolveStorageRef_vote_senderVoted evm I
  have hread :
      readStorage? ballotConfig evm (voteSenderEvaledRef I "voted") (.elem .bool) =
        .ok (.bool true) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := voteSenderPackedSlot I, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool true)
    rw [voteStorageLocLoad_bool_offset0_true evm (voteSenderPackedSlot I)]
    simpa [voteSenderVotedByteCurrent, voteSenderPackedCurrent] using hvoted
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_vote_sender_not_voted_true (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : voteSenderVotedByteCurrent evm I = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.unary .not (.storage (aliasF "sender" "voted"))) = .ok (.bool true) := by
  have hstorage := evalExpr_vote_sender_voted_false evm I hvoted
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem evalExpr_vote_sender_not_voted_false (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : voteSenderVotedByteCurrent evm I ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.unary .not (.storage (aliasF "sender" "voted"))) = .ok (.bool false) := by
  have hstorage := evalExpr_vote_sender_voted_true evm I hvoted
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem voteArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat (voteProposalWord I).toNat)) = .ok () := by
  have hboundStorage :
      (voteProposalWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [voteProposalsLengthCurrent] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hboundStorage]

theorem voteArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : ¬ (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat (voteProposalWord I).toNat)) = .revert := by
  have hboundStorage :
      ¬ (voteProposalWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [voteProposalsLengthCurrent] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) ≤
        (voteProposalWord I).toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout, ballotContract,
    ballotStorageDecls, proposalStructTy, uint256St, bytes32St, ballotStorageLocLoad_uint256,
    hleStorage]

theorem evalStorageRef_vote_proposalCount (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (proposalF (.var "proposal") "voteCount") = .ok (voteProposalCountEvaledRef I) := by
  have hproposalGet : (voteAliasStore I).get? "proposal" = some (voteProposalValue I) := by
    unfold voteAliasStore
    rw [store_get_ne]
    · exact store_get_self ∅ "proposal" (voteProposalValue I)
    · decide
  have hproposal :
      evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
        (.var "proposal") = .ok (voteProposalValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((voteAliasStore I).get? "proposal") = .ok (voteProposalValue I)
    rw [hproposalGet]
    rfl
  have hboundsOk :
      arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
        (.int (Int.ofNat (voteProposalWord I).toNat)) = .ok () :=
    voteArrayIndexInBounds_ok evm I hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hproposal, voteProposalValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    List.nil_append]
  rw [hboundsOk]
  simp [voteProposalCountEvaledRef]

theorem evalStorageRef_vote_proposalCount_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : ¬ (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (proposalF (.var "proposal") "voteCount") = .revert := by
  have hproposalGet : (voteAliasStore I).get? "proposal" = some (voteProposalValue I) := by
    unfold voteAliasStore
    rw [store_get_ne]
    · exact store_get_self ∅ "proposal" (voteProposalValue I)
    · decide
  have hproposal :
      evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
        (.var "proposal") = .ok (voteProposalValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((voteAliasStore I).get? "proposal") = .ok (voteProposalValue I)
    rw [hproposalGet]
    rfl
  have hboundsRevert :
      arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
        (.int (Int.ofNat (voteProposalWord I).toNat)) = .revert :=
    voteArrayIndexInBounds_revert evm I hbound
  simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    hproposal, voteProposalValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    List.nil_append]
  rw [hboundsRevert]

theorem evalExpr_vote_proposal_count (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.storage (proposalF (.var "proposal") "voteCount")) =
        .ok (.int (Int.ofNat (voteProposalCountCurrent evm I).toNat)) := by
  have hbase : (voteAliasStore I).get? (proposalF (.var "proposal") "voteCount").base = none := by
    simp [voteAliasStore, voteStore, proposalF]
  have hty :
      storageTypeAt? ballotContract.storage (voteProposalCountEvaledRef I) =
        some (.elem (.int uint256Int)) := by
    simp [voteProposalCountEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
      ballotStorageDecls, proposalStructTy, uint256St]
  have hloc :
      ballotConfig.storage.layout (voteProposalCountEvaledRef I) =
        fun _ => some (wordLoc (voteProposalCountSlot I)) := by
    funext evm'
    simp [voteProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
      voteProposalCountSlot_spec, u256_add_comm]
  have hload :
      storageLocLoad evm (wordLoc (voteProposalCountSlot I)) =
        .int (Int.ofNat (voteProposalCountCurrent evm I).toNat) := by
    simpa [voteProposalCountCurrent] using
      (ballotStorageLocLoad_uint256 evm (voteProposalCountSlot I))
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_vote_proposalCount evm I hbound) (hty := hty) (hloc := hloc)]
  simpa using congrArg EvalResult.ok hload

theorem evalExpr_vote_proposal (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (.var "proposal") = .ok (voteProposalValue I) := by
  have hproposalGet : (voteAliasStore I).get? "proposal" = some (voteProposalValue I) := by
    unfold voteAliasStore
    rw [store_get_ne]
    · exact store_get_self ∅ "proposal" (voteProposalValue I)
    · decide
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((voteAliasStore I).get? "proposal") = .ok (voteProposalValue I)
  rw [hproposalGet]
  rfl

theorem evalExpr_vote_proposal_count_add (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat)
    (hfit : (voteProposalCountCurrent evm I).toNat + (voteSenderWeightCurrent evm I).toNat <
      UInt256.size) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (u256 (.binary .add (.storage (proposalF (.var "proposal") "voteCount"))
        (.storage (aliasF "sender" "weight")))) =
        .ok (.int (Int.ofNat (UInt256.add (voteProposalCountCurrent evm I)
          (voteSenderWeightCurrent evm I)).toNat)) := by
  have hcount := evalExpr_vote_proposal_count evm I hbound
  have hweight := evalExpr_vote_sender_weight evm I
  have hlt : ¬ Int.ofNat ((voteProposalCountCurrent evm I).toNat +
      (voteSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat ((voteProposalCountCurrent evm I).toNat +
      (voteSenderWeightCurrent evm I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat ((voteProposalCountCurrent evm I).toNat) +
        Int.ofNat ((voteSenderWeightCurrent evm I).toNat) =
          Int.ofNat ((voteProposalCountCurrent evm I).toNat +
            (voteSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  have hword :
      (UInt256.add (voteProposalCountCurrent evm I) (voteSenderWeightCurrent evm I)).toNat =
        (voteProposalCountCurrent evm I).toNat + (voteSenderWeightCurrent evm I).toNat := by
    change ((voteProposalCountCurrent evm I) + (voteSenderWeightCurrent evm I)).toNat =
      (voteProposalCountCurrent evm I).toNat + (voteSenderWeightCurrent evm I).toNat
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

theorem evalExpr_vote_proposal_count_add_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat)
    (hover : UInt256.size ≤
      (voteProposalCountCurrent evm I).toNat + (voteSenderWeightCurrent evm I).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (u256 (.binary .add (.storage (proposalF (.var "proposal") "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hcount := evalExpr_vote_proposal_count evm I hbound
  have hweight := evalExpr_vote_sender_weight evm I
  have hge : Int.ofNat ((voteProposalCountCurrent evm I).toNat +
      (voteSenderWeightCurrent evm I).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hnonneg : ¬ Int.ofNat ((voteProposalCountCurrent evm I).toNat +
      (voteSenderWeightCurrent evm I).toNat) < 0 := by
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hadd :
      Int.ofNat ((voteProposalCountCurrent evm I).toNat) +
        Int.ofNat ((voteSenderWeightCurrent evm I).toNat) =
          Int.ofNat ((voteProposalCountCurrent evm I).toNat +
            (voteSenderWeightCurrent evm I).toNat) := by
    exact (Int.natCast_add _ _).symm
  simp [u256, evalExpr?, EvalResult.bind, bind, hcount, hweight, evalBinaryOp?, uint256Int,
    hadd]
  intro _
  exact_mod_cast hover

theorem voteAssignVoted (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      .storage (aliasF "sender" "voted") (.bool true) =
        .ok ({ contract := ballotContract, locals := voteAliasStore I },
          voteAfterVotedState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_vote_senderVoted evm I, bind, EvalResult.bind,
    EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, voteSenderEvaledRef, voteSenderPackedSlot,
    voteSenderSlot]
  rw [voteStorageLocStore_bool_true_offset0]
  simp [voteAfterVotedState, voteSenderVotedStoreCurrent, voteSenderPackedCurrent,
    voteSenderPackedSlot, voteSenderSlot]

theorem voteAssignVote (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I }
      (voteAfterVotedState evm I) .storage (aliasF "sender" "vote") (voteProposalValue I) =
        .ok ({ contract := ballotContract, locals := voteAliasStore I },
          voteAfterVoteState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_vote_senderVote (voteAfterVotedState evm I) I,
    bind, EvalResult.bind, EvalResult.ofOption, pure]
  simp only [ballotConfig, ballotStorageLayout, voteSenderEvaledRef, voteSenderVoteSlot,
    voteSenderSlot]
  rw [voteStorageLocStore_uint256]
  simp [voteAfterVoteState, voteAfterVotedState, voteProposalValue, voteSenderVoteSlot,
    voteSenderSlot, Solm.EVM.storageStore]

theorem voteAssignProposalCount (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat)
    (_hfit : (voteProposalCountCurrent evm I).toNat + (voteSenderWeightCurrent evm I).toNat <
      UInt256.size) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      .storage (proposalF (.var "proposal") "voteCount")
      (.int (Int.ofNat (UInt256.add (voteProposalCountCurrent evm I)
        (voteSenderWeightCurrent evm I)).toNat)) =
        .ok ({ contract := ballotContract, locals := voteAliasStore I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (voteProposalCountSlot I)
            (UInt256.add (voteProposalCountCurrent evm I) (voteSenderWeightCurrent evm I))) := by
  apply assignStorageRef_storage_scalar (er := voteProposalCountEvaledRef I)
      (loc := wordLoc (voteProposalCountSlot I)) (ty := .elem (.int uint256Int))
      (hbase := by simp [voteAliasStore, voteStore, proposalF])
      (her := evalStorageRef_vote_proposalCount evm I hbound)
      (hty := by simp [storageTypeAt?, voteProposalCountEvaledRef, ballotContract,
        ballotStorageDecls, proposalStructTy, uint256St, storageTypeStep?])
      (hloc := by
        funext evm'
        simp [voteProposalCountEvaledRef, ballotConfig, ballotStorageLayout,
          voteProposalCountSlot_spec, u256_add_comm])
  rw [voteStorageLocStore_uint256]

theorem evalExpr_vote_proposal_count_add_oob_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : ¬ (voteProposalWord I).toNat < (voteProposalsLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := voteAliasStore I } evm
      (u256 (.binary .add (.storage (proposalF (.var "proposal") "voteCount"))
        (.storage (aliasF "sender" "weight")))) = .revert := by
  have hrevert := evalStorageRef_vote_proposalCount_revert evm I hbound
  have hbase : (voteAliasStore I).get? (proposalF (.var "proposal") "voteCount").base = none := by
    simp [voteAliasStore, voteStore, proposalF]
  rw [u256, evalExpr?]
  simp only [evalExpr?, hbase, resolveStorageRef?, hrevert, EvalResult.bind, bind]

theorem ballotVoteBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hweight : voteSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByteCurrent evm I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthCurrent (voteAfterVoteState evm I)).toNat)
    (hfit :
      (voteProposalCountCurrent (voteAfterVoteState evm I) I).toNat +
          (voteSenderWeightCurrent (voteAfterVoteState evm I) I).toNat <
        UInt256.size) :
    ExecTransitionBody ballotConfig ballotContract evm (voteStore I) voteTransition.body
      (.returned { contract := ballotContract, locals := voteAliasStore I }
        (voteFinalState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_vote_sender evm I hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_weight_ne_zero_true evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (voteAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_vote_proposal (voteAfterVotedState evm I) I)
      (voteAssignVote evm I)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  apply ExecStmt.assign
  · exact evalExpr_vote_proposal_count_add (voteAfterVoteState evm I) I hbound hfit
  · simpa [voteFinalState, voteUpdatedProposalCountCurrent] using
      voteAssignProposalCount (voteAfterVoteState evm I) I hbound hfit

theorem ballotVoteBodyReverts_weight (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hweight : voteSenderWeightCurrent evm I = ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (voteStore I) voteTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.letStorage (resolveStorageRef_vote_sender evm I hsource)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse
          (evalExpr_vote_sender_weight_ne_zero_false evm I hweight))

theorem ballotVoteBodyReverts_voted (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hweight : voteSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByteCurrent evm I ≠ ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (voteStore I) voteTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.letStorage (resolveStorageRef_vote_sender evm I hsource)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue (evalExpr_vote_sender_weight_ne_zero_true evm I hweight)) <|
          ExecBlock.consRevert (ExecStmt.requireFalse
            (evalExpr_vote_sender_not_voted_false evm I hvoted))

theorem ballotVoteBodyReverts_oob (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hweight : voteSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByteCurrent evm I = ⟨0⟩)
    (hbound :
      ¬ (voteProposalWord I).toNat <
        (voteProposalsLengthCurrent (voteAfterVoteState evm I)).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (voteStore I) voteTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_vote_sender evm I hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_weight_ne_zero_true evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (voteAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_vote_proposal (voteAfterVotedState evm I) I)
      (voteAssignVote evm I)) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_vote_proposal_count_add_oob_revert (voteAfterVoteState evm I) I hbound))

theorem ballotVoteBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hweight : voteSenderWeightCurrent evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByteCurrent evm I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthCurrent (voteAfterVoteState evm I)).toNat)
    (hover :
      UInt256.size ≤
        (voteProposalCountCurrent (voteAfterVoteState evm I) I).toNat +
          (voteSenderWeightCurrent (voteAfterVoteState evm I) I).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (voteStore I) voteTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_vote_sender evm I hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_weight_ne_zero_true evm I hweight)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_vote_sender_not_voted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (voteAssignVoted evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_vote_proposal (voteAfterVotedState evm I) I)
      (voteAssignVote evm I)) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalExpr_vote_proposal_count_add_revert (voteAfterVoteState evm I) I hbound hover))

/-! ## EVM scratch memory -/

noncomputable def voteKeyMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (voteSourceWord I)).write 0 solcFreePtrMem 0 32

noncomputable def voteHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (voteKeyMem I) 32 32

noncomputable def voteProposalBaseMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0 (voteHashMem I) 0 32

theorem voteKeyMem_size (I : ExecutionEnv) : (voteKeyMem I).size = 96 := by
  unfold voteKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem voteHashMem_size (I : ExecutionEnv) : (voteHashMem I).size = 96 := by
  unfold voteHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [voteKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteKeyMem_size, toByteArray_size]
  omega

theorem voteProposalBaseMem_size (I : ExecutionEnv) : (voteProposalBaseMem I).size = 96 := by
  unfold voteProposalBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [voteHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteHashMem_size, toByteArray_size]
  omega

theorem voteKeyMem_read0 (I : ExecutionEnv) :
    (voteKeyMem I).readWithPadding 0 32 = UInt256.toByteArray (voteSourceWord I) := by
  unfold voteKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray (voteSourceWord I)).extract 0 32 =
      UInt256.toByteArray (voteSourceWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (voteSourceWord I)).size ≤ 32
          rw [toByteArray_size])]

theorem voteKeyMem_read64 (I : ExecutionEnv) :
    (voteKeyMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem voteHashMem_read0 (I : ExecutionEnv) :
    (voteHashMem I).readWithPadding 0 32 = UInt256.toByteArray (voteSourceWord I) := by
  unfold voteHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [voteKeyMem_size]; omega) (by omega),
    voteKeyMem_read0]

theorem voteHashMem_read32 (I : ExecutionEnv) :
    (voteHashMem I).readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold voteHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [voteKeyMem_size]; omega),
    show (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem voteHashMem_read64 (I : ExecutionEnv) :
    (voteHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [voteKeyMem_size]; omega) (by omega)
      (by rw [voteKeyMem_size]),
    voteKeyMem_read64]

theorem voteHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (voteHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((voteHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [voteHashMem_size]; decide) (by decide)
    (voteHashMem_read64 I)

theorem voteProposalBaseMem_read0 (I : ExecutionEnv) :
    (voteProposalBaseMem I).readWithPadding 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold voteProposalBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [voteHashMem_size]; omega),
    show (UInt256.toByteArray (⟨2⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨2⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem voteProposalsDataBaseKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((voteProposalBaseMem I).readWithPadding 0 32))) = proposalsDataBase := by
  rw [voteProposalBaseMem_read0]
  unfold proposalsDataBase
  exact keccakSlot_eq _

theorem voteHashMem_read0_64 (I : ExecutionEnv) :
    (voteHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (voteSourceWord I) ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [voteHashMem_size]; omega)]
  unfold voteHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [voteKeyMem_size]; omega)]
  have hsourceFull :
      (UInt256.toByteArray (voteSourceWord I)).extract 0 32 =
        UInt256.toByteArray (voteSourceWord I) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (voteSourceWord I)).size ≤ 32
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
      (voteKeyMem I).extract 0 32 = UInt256.toByteArray (voteSourceWord I) := by
    have hread := voteKeyMem_read0 I
    rw [readWithPadding_eq_extract _ 0 (by rw [voteKeyMem_size]; omega)] at hread
    exact hread
  have hempty : (voteKeyMem I).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hbaseFull]
  rw [ByteArray.append_assoc]
  rw [extract_append_span ((voteKeyMem I).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (voteKeyMem I).extract (32 + 32) (voteKeyMem I).size) 0 64
      (by omega) (by rw [ByteArray.size_extract, voteKeyMem_size]; omega)]
  rw [show ((voteKeyMem I).extract 0 32).size = 32 by
      rw [ByteArray.size_extract, voteKeyMem_size]; omega]
  rw [show 64 - 32 = 32 from rfl]
  rw [hkey0, hsourceFull]
  rw [extract_append_left _ _ 0 32 (by rw [toByteArray_size])]
  rw [hbaseFull]

theorem voteSenderKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((voteHashMem I).readWithPadding 0 64))) = voteSenderSlot I := by
  rw [voteHashMem_read0_64, keccakSlot_eq, ← voteSenderSlot_eq_hash I]

def voteErrorSelector : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

def voteWeightStringRaw : UInt256 :=
  ⟨0x486173206e6f20726967687420746f20766f7465⟩

def voteWeightStringWord : UInt256 :=
  UInt256.shiftLeft voteWeightStringRaw ⟨96⟩

def voteVotedStringRaw : UInt256 :=
  ⟨0x20b63932b0b23c903b37ba32b217⟩

def voteVotedStringWord : UInt256 :=
  UInt256.shiftLeft voteVotedStringRaw ⟨145⟩

noncomputable def voteErrorMem0 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray voteErrorSelector).write 0 (voteHashMem I) 128 32

noncomputable def voteErrorMem1 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (voteErrorMem0 I) 132 32

noncomputable def voteWeightErrorMem2 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨20⟩ : UInt256)).write 0 (voteErrorMem1 I) 164 32

noncomputable def voteWeightErrorMem3 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray voteWeightStringWord).write 0 (voteWeightErrorMem2 I) 196 32

noncomputable def voteVotedErrorMem2 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨14⟩ : UInt256)).write 0 (voteErrorMem1 I) 164 32

noncomputable def voteVotedErrorMem3 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray voteVotedStringWord).write 0 (voteVotedErrorMem2 I) 196 32

theorem voteErrorMem0_size (I : ExecutionEnv) : (voteErrorMem0 I).size = 160 := by
  unfold voteErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [voteHashMem_size]; omega)
      (by rw [voteHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, voteHashMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num,
    toByteArray_size]

theorem voteErrorMem1_size (I : ExecutionEnv) : (voteErrorMem1 I).size = 164 := by
  unfold voteErrorMem1
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [voteErrorMem0_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteErrorMem0_size, toByteArray_size]
  omega

theorem voteWeightErrorMem2_size (I : ExecutionEnv) :
    (voteWeightErrorMem2 I).size = 196 := by
  unfold voteWeightErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size]) (by rw [voteErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteErrorMem1_size, toByteArray_size]
  omega

theorem voteWeightErrorMem3_size (I : ExecutionEnv) :
    (voteWeightErrorMem3 I).size = 228 := by
  unfold voteWeightErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [voteWeightErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteWeightErrorMem2_size, toByteArray_size]
  omega

theorem voteVotedErrorMem2_size (I : ExecutionEnv) :
    (voteVotedErrorMem2 I).size = 196 := by
  unfold voteVotedErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size]) (by rw [voteErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteErrorMem1_size, toByteArray_size]
  omega

theorem voteVotedErrorMem3_size (I : ExecutionEnv) :
    (voteVotedErrorMem3 I).size = 228 := by
  unfold voteVotedErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [voteVotedErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, voteVotedErrorMem2_size, toByteArray_size]
  omega

theorem voteErrorMem0_read64 (I : ExecutionEnv) :
    (voteErrorMem0 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [voteHashMem_size]; omega)
      (by rw [voteHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, voteHashMem_size, ByteArray_zeroes_size,
        show 128 - 96 = 32 from by norm_num,
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, voteHashMem_size, ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [voteHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [voteHashMem_size])]
  exact voteHashMem_read64 I

theorem voteErrorMem1_read64 (I : ExecutionEnv) :
    (voteErrorMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteErrorMem1
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [voteErrorMem0_size]; omega) (by omega),
    voteErrorMem0_read64]

theorem voteWeightErrorMem2_read64 (I : ExecutionEnv) :
    (voteWeightErrorMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteWeightErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [voteErrorMem1_size]) (by omega),
    voteErrorMem1_read64]

theorem voteWeightErrorMem3_read64 (I : ExecutionEnv) :
    (voteWeightErrorMem3 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteWeightErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [voteWeightErrorMem2_size]) (by omega),
    voteWeightErrorMem2_read64]

theorem voteVotedErrorMem2_read64 (I : ExecutionEnv) :
    (voteVotedErrorMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteVotedErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [voteErrorMem1_size]) (by omega),
    voteErrorMem1_read64]

theorem voteVotedErrorMem3_read64 (I : ExecutionEnv) :
    (voteVotedErrorMem3 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold voteVotedErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [voteVotedErrorMem2_size]) (by omega),
    voteVotedErrorMem2_read64]

theorem voteWeightErrorMem3_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (voteWeightErrorMem3 I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((voteWeightErrorMem3 I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [voteWeightErrorMem3_size]; decide) (by decide)
    (voteWeightErrorMem3_read64 I)

theorem voteVotedErrorMem3_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (voteVotedErrorMem3 I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((voteVotedErrorMem3 I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [voteVotedErrorMem3_size]; decide) (by decide)
    (voteVotedErrorMem3_read64 I)

theorem voteProposalCountSlot_evm (I : ExecutionEnv) :
    (⟨1⟩ : UInt256) + (UInt256.mul ⟨2⟩ (voteProposalWord I) + proposalsDataBase) =
      voteProposalCountSlot I := by
  unfold voteProposalCountSlot
  rw [u256_mul_comm ⟨2⟩ (voteProposalWord I)]
  exact u256_add_comm _ _

end Ballot

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM

end Reasoning.Theory

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

end Reasoning.Reach

namespace Ballot

/-! ## EVM trace: ABI decoder bridge -/

theorem ballotVoteX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1747⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨151⟩, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd137⟩ := hreach
  exact ⟨_, _, evm_run rd137 with [
    jumpdest, push2 ⟨156⟩, push2 ⟨151⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1747⟩,
    jump (by jump_dest) ]⟩

theorem ballotVoteX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨425⟩
      [voteProposalWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1747⟩ := ballotVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  obtain ⟨_, _, rd151⟩ := RD.ballotDecodeUint256Ok1747 rd1747 hslt (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd151 with [jumpdest, push2 ⟨425⟩, jump (by jump_dest)]⟩

theorem ballotVoteX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1747⟩ := ballotVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeUint256Revert1747 rd1747 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotVoteX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1747⟩ := ballotVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeUint256Revert1747 rd1747 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## EVM trace: body prefix -/

theorem ballotVoteX_afterWeight {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨516⟩
      [voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd425⟩ := ballotVoteX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  have rd440 := evm_run rd425 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (voteKeyMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by simp [voteKeyMem, voteSourceWord]) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (voteHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by
        change (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (voteKeyMem I) 32 32 =
          voteHashMem I
        rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (voteSenderSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (voteSenderKeccakSlot I) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd442₀⟩ := rd440.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd442⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [voteSenderWeightWord σ I, voteSenderSlot I, ⟨0⟩, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [voteSenderWeightWord, initState] using rd442₀⟩
  have rd444 := evm_run rd442 with [swap1, swap2, sub]
  exact ⟨_, _, evm_run rd444 with [
    push2 ⟨516⟩, jumpiT (u256_zero_sub_ne_zero hweight) (by jump_dest)]⟩

theorem ballotVoteX_afterNotVoted {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨586⟩
      [voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd516⟩ := ballotVoteX_afterWeight (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hweight hreach
  have rd521 := evm_run rd516 with [jumpdest, push1 ⟨1⟩, dup2, add]
  obtain ⟨_, _, rd522₀⟩ := rd521.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd522⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [voteSenderPackedWord σ I, voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [voteSenderPackedWord, voteSenderPackedSlot, initState] using rd522₀⟩
  have rd525 := evm_run rd522 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (voteSenderPackedWord σ I)) = ⟨1⟩ := by
    rw [u256_land_comm]
    change UInt256.isZero (voteSenderVotedByte σ I) = ⟨1⟩
    rw [hvoted]
    decide
  have rd525' := rd525
  rw [hzero] at rd525'
  exact ⟨_, _, evm_run rd525' with [push2 ⟨586⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotVoteX_afterSenderStores {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨611⟩
      [⟨2⟩, voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
  obtain ⟨_, _, rd586⟩ := ballotVoteX_afterNotVoted (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hweight hvoted hreach
  have rd593 := evm_run rd586 with [jumpdest, push1 ⟨1⟩, dup2, dup2, add, dup1]
  obtain ⟨_, _, rd594⟩ := rd593.sload (by decide) (by evm_ov)
  have rd600 := evm_run rd594 with [push1 ⟨255⟩, not, and, swap1, swap2]
  have rd601 := RD.or rd600 (by decide) (by evm_ov)
  have rd602 := evm_run rd601 with [swap1]
  obtain ⟨_, _, rd603⟩ := rd602.sstore hperm (by decide) (by evm_ov)
  have rd610 := evm_run rd603 with [push1 ⟨2⟩, dup1, dup3, add, dup4, swap1]
  obtain ⟨_, _, rd611⟩ := rd610.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [voteAfterVoteMap, voteAfterVotedMap, voteSenderVotedStoreWord,
      voteSenderPackedWord, voteSenderPackedSlot, voteSenderVoteSlot, u256_add_comm,
      u256_land_comm, u256_lor_comm, initState] using rd611⟩

theorem ballotVoteX_afterBounds {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨633⟩
      [voteProposalWord I, ⟨2⟩, voteSenderWeightWord (voteAfterVoteMap σ I) I,
        voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
  obtain ⟨_, _, rd611⟩ := ballotVoteX_afterSenderStores (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hreach
  have rd612 := evm_run rd611 with [dup2]
  obtain ⟨_, _, rd613₀⟩ := rd612.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd613⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [voteSenderWeightWord (voteAfterVoteMap σ I) I, ⟨2⟩, voteSenderSlot I,
        voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
    exact ⟨_, _, by simpa [voteSenderWeightWord, initState] using rd613₀⟩
  have rd614 := evm_run rd613 with [dup2]
  obtain ⟨_, _, rd615₀⟩ := rd614.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd615⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨615⟩
      [voteProposalsLengthWord (voteAfterVoteMap σ I) I,
        voteSenderWeightWord (voteAfterVoteMap σ I) I, ⟨2⟩, voteSenderSlot I,
        voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
    exact ⟨_, _, by simpa [voteProposalsLengthWord, initState] using rd615₀⟩
  have hlt : UInt256.lt (voteProposalWord I) (voteProposalsLengthWord (voteAfterVoteMap σ I) I)
      = ⟨1⟩ :=
    ult_one hbound
  have rd621 := evm_run rd615 with [swap1, swap2, swap1, dup5, swap1, dup2, lt]
  have rd621' := rd621
  rw [hlt] at rd621'
  exact ⟨_, _, evm_run rd621' with [push2 ⟨633⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotVoteX_toCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1835⟩
      [voteProposalCountWord (voteAfterVoteMap σ I) I,
        voteSenderWeightWord (voteAfterVoteMap σ I) I, ⟨662⟩, ⟨0⟩,
        voteProposalCountSlot I, voteSenderWeightWord (voteAfterVoteMap σ I) I,
        voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteProposalBaseMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, voteAfterVoteMap σ I) k C := by
  obtain ⟨_, _, rd633⟩ := ballotVoteX_afterBounds (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hbound hreach
  have rd652 := evm_run rd633 with [
    jumpdest, swap1, push0,
    raw mstore 0 (voteProposalBaseMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by simp [voteProposalBaseMem]) (by decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
      mem_cost (voteProposalsDataBaseKeccak I) (by decide) (by evm_ov),
    swap1, push1 ⟨2⟩, mul, add, push1 ⟨1⟩, add, push0, dup3, dup3]
  obtain ⟨_, _, rd653⟩ := rd652.sload (by decide) (by evm_ov)
  have rd1835 := evm_run rd653 with [
    push2 ⟨662⟩, swap2, swap1, push2 ⟨1835⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [voteProposalCountWord, voteProposalCountSlot_evm, initState] using rd1835⟩

theorem ballotVoteX_afterCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hfit :
      (voteProposalCountWord (voteAfterVoteMap σ I) I).toNat +
          (voteSenderWeightWord (voteAfterVoteMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨662⟩
      [voteSenderWeightWord (voteAfterVoteMap σ I) I +
          voteProposalCountWord (voteAfterVoteMap σ I) I,
        ⟨0⟩, voteProposalCountSlot I, voteSenderWeightWord (voteAfterVoteMap σ I) I,
        voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteProposalBaseMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, voteAfterVoteMap σ I) k C := by
  obtain ⟨_, _, rd1835⟩ := ballotVoteX_toCheckedAdd (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hbound hreach
  let count := voteProposalCountWord (voteAfterVoteMap σ I) I
  let weight := voteSenderWeightWord (voteAfterVoteMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hsumNat : (weight + count).toNat = weight.toNat + count.toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by simpa [count, weight, Nat.add_comm] using hfit)
  have hgt : UInt256.gt count (weight + count) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsumNat]; omega)
  have rd1842' := rd1842
  rw [show voteProposalCountWord (voteAfterVoteMap σ I) I = count from rfl,
      show voteSenderWeightWord (voteAfterVoteMap σ I) I = weight from rfl, hgt,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1842'
  have rd1866 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiT (by decide) (by jump_dest)]
  have rd662 := evm_run rd1866 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [count, weight] using rd662⟩

theorem ballotVoteX_success {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hfit :
      (voteProposalCountWord (voteAfterVoteMap σ I) I).toNat +
          (voteSenderWeightWord (voteAfterVoteMap σ I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, voteSuccessMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd662⟩ := ballotVoteX_afterCheckedAdd (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hbound hfit hreach
  have rd665 := evm_run rd662 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd666⟩ := rd665.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd666 with [pop, pop, pop, pop, jump (by jump_dest), jumpdest]
  exact by
    simpa [voteSuccessMap, voteUpdatedProposalCount, u256_add_comm] using
      rd156.stop (by decide) (by evm_ov)

theorem ballotVoteX_weightRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd425⟩ := ballotVoteX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  have rd440 := evm_run rd425 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (voteKeyMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by simp [voteKeyMem, voteSourceWord]) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (voteHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by
        change (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (voteKeyMem I) 32 32 =
          voteHashMem I
        rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (voteSenderSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (voteSenderKeccakSlot I) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd442₀⟩ := rd440.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd442⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [voteSenderWeightWord σ I, voteSenderSlot I, ⟨0⟩, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [voteSenderWeightWord, initState] using rd442₀⟩
  have rd444 := evm_run rd442 with [swap1, swap2, sub]
  have hsubzero : UInt256.sub ⟨0⟩ (voteSenderWeightWord σ I) = ⟨0⟩ := by
    rw [hweight]
    decide
  have rd444' := rd444
  rw [hsubzero] at rd444'
  have rd449 := evm_run rd444' with [push2 ⟨516⟩, jumpiNT (by decide)]
  have rd452 := evm_run rd449 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (voteHashMem_mload64 I) (by decide) (by evm_ov)]
  have rd456 := rd452.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd475 := evm_run rd456 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (voteErrorMem0 I) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (voteErrorMem1 I) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (voteWeightErrorMem2 I) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd496 := rd475.pushConst voteWeightStringRaw (width := 20) (op := .PUSH20)
    (by decide) (by decide) (by evm_ov)
  exact evm_run rd496 with [
    push1 ⟨96⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3 (voteWeightErrorMem3 I) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (voteWeightErrorMem3_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem ballotVoteX_votedRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd516⟩ := ballotVoteX_afterWeight (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hweight hreach
  have rd521 := evm_run rd516 with [jumpdest, push1 ⟨1⟩, dup2, add]
  obtain ⟨_, _, rd522₀⟩ := rd521.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd522⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [voteSenderPackedWord σ I, voteSenderSlot I, voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [voteSenderPackedWord, voteSenderPackedSlot, initState] using rd522₀⟩
  have rd525 := evm_run rd522 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (voteSenderPackedWord σ I)) = ⟨0⟩ := by
    rw [u256_land_comm]
    change UInt256.isZero (voteSenderVotedByte σ I) = ⟨0⟩
    exact isZero_eq_zero_of_ne hvoted
  have rd525' := rd525
  rw [hzero] at rd525'
  have rd530 := evm_run rd525' with [push2 ⟨586⟩, jumpiNT (by decide)]
  have rd533 := evm_run rd530 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (voteHashMem_mload64 I) (by decide) (by evm_ov)]
  have rd537 := rd533.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd556 := evm_run rd537 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (voteErrorMem0 I) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (voteErrorMem1 I) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨14⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (voteVotedErrorMem2 I) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd571 := rd556.pushConst voteVotedStringRaw (width := 14) (op := .PUSH14)
    (by decide) (by decide) (by evm_ov)
  exact evm_run rd571 with [
    push1 ⟨145⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3 (voteVotedErrorMem3 I) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (voteVotedErrorMem3_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem ballotVoteX_oob {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      ¬ (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd611⟩ := ballotVoteX_afterSenderStores (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hreach
  have rd612 := evm_run rd611 with [dup2]
  obtain ⟨_, _, rd613₀⟩ := rd612.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd613⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [voteSenderWeightWord (voteAfterVoteMap σ I) I, ⟨2⟩, voteSenderSlot I,
        voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
    exact ⟨_, _, by simpa [voteSenderWeightWord, initState] using rd613₀⟩
  have rd614 := evm_run rd613 with [dup2]
  obtain ⟨_, _, rd615₀⟩ := rd614.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd615⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨615⟩
      [voteProposalsLengthWord (voteAfterVoteMap σ I) I,
        voteSenderWeightWord (voteAfterVoteMap σ I) I, ⟨2⟩, voteSenderSlot I,
        voteProposalWord I, ⟨156⟩, sel]
      (voteHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, voteAfterVoteMap σ I) k C := by
    exact ⟨_, _, by simpa [voteProposalsLengthWord, initState] using rd615₀⟩
  have hlt : UInt256.lt (voteProposalWord I) (voteProposalsLengthWord (voteAfterVoteMap σ I) I)
      = ⟨0⟩ :=
    ult_zero (Nat.le_of_not_gt hbound)
  have rd621 := evm_run rd615 with [swap1, swap2, swap1, dup5, swap1, dup2, lt]
  have rd621' := rd621
  rw [hlt] at rd621'
  have rd1815 := evm_run rd621' with [
    push2 ⟨633⟩, jumpiNT (by decide), push2 ⟨633⟩, push2 ⟨1815⟩, jump (by jump_dest)]
  exact RD.ballotPanic32Revert1815 rd1815
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotVoteOverflowGt (count weight : UInt256)
    (hover : UInt256.size ≤ count.toNat + weight.toNat) :
    UInt256.gt count (weight + count) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ weight.toNat + count.toNat := by
    omega
  have hsum_lt2 : weight.toNat + count.toNat < 2 * UInt256.size := by
    have hc : count.toNat < UInt256.size := count.val.isLt
    have hw : weight.toNat < UInt256.size := weight.val.isLt
    omega
  have hmod : (weight.toNat + count.toNat) % UInt256.size =
      weight.toNat + count.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (weight + count).toNat = weight.toNat + count.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (count > weight + count)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show count.toNat > (weight + count).toNat
    rw [haddNat]
    have hw : weight.toNat < UInt256.size := weight.val.isLt
    omega

theorem ballotVoteX_overflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hweight : voteSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat < (voteProposalsLengthWord (voteAfterVoteMap σ I) I).toNat)
    (hover : UInt256.size ≤
      (voteProposalCountWord (voteAfterVoteMap σ I) I).toNat +
        (voteSenderWeightWord (voteAfterVoteMap σ I) I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1835⟩ := ballotVoteX_toCheckedAdd (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hperm hweight hvoted hbound hreach
  let count := voteProposalCountWord (voteAfterVoteMap σ I) I
  let weight := voteSenderWeightWord (voteAfterVoteMap σ I) I
  have rd1842 := evm_run rd1835 with [jumpdest, dup1, dup3, add, dup1, dup3, gt, iszero]
  have hgt : UInt256.gt count (weight + count) = ⟨1⟩ := by
    exact ballotVoteOverflowGt count weight (by simpa [count, weight] using hover)
  have rd1842' := rd1842
  rw [show voteProposalCountWord (voteAfterVoteMap σ I) I = count from rfl,
      show voteSenderWeightWord (voteAfterVoteMap σ I) I = weight from rfl, hgt,
      show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1842'
  have rd1847 := evm_run rd1842' with [push2 ⟨1866⟩, jumpiNT (by decide)]
  exact RD.ballotPanic11Revert1847 rd1847
    (by simp only [List.length_cons, List.length_nil]; omega)

@[simp] theorem voteStorageStore_executionEnv (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;> rfl

theorem voteSenderWeightCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    voteSenderWeightCurrent (initState cA gh bl σ σ₀ g A I) I = voteSenderWeightWord σ I := by
  rfl

theorem voteSenderVotedByteCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    voteSenderVotedByteCurrent (initState cA gh bl σ σ₀ g A I) I = voteSenderVotedByte σ I := by
  rfl

theorem voteProposalsLengthCurrent_afterVoteState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    voteProposalsLengthCurrent (voteAfterVoteState (initState cA gh bl σ σ₀ g A I) I) =
      voteProposalsLengthWord (voteAfterVoteMap σ I) I := by
  unfold voteProposalsLengthCurrent voteProposalsLengthWord voteAfterVoteState
    voteAfterVotedState voteAfterVoteMap voteAfterVotedMap voteSenderVotedStoreCurrent
    voteSenderVotedStoreWord voteSenderPackedCurrent voteSenderPackedWord
    Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  simp [initState, storageStore_accountMap]

theorem voteProposalCountCurrent_afterVoteState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    voteProposalCountCurrent (voteAfterVoteState (initState cA gh bl σ σ₀ g A I) I) I =
      voteProposalCountWord (voteAfterVoteMap σ I) I := by
  unfold voteProposalCountCurrent voteProposalCountWord voteAfterVoteState
    voteAfterVotedState voteAfterVoteMap voteAfterVotedMap voteSenderVotedStoreCurrent
    voteSenderVotedStoreWord voteSenderPackedCurrent voteSenderPackedWord
    Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  simp [initState, storageStore_accountMap]

theorem voteSenderWeightCurrent_afterVoteState_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    voteSenderWeightCurrent (voteAfterVoteState (initState cA gh bl σ σ₀ g A I) I) I =
      voteSenderWeightWord (voteAfterVoteMap σ I) I := by
  unfold voteSenderWeightCurrent voteSenderWeightWord voteAfterVoteState
    voteAfterVotedState voteAfterVoteMap voteAfterVotedMap voteSenderVotedStoreCurrent
    voteSenderVotedStoreWord voteSenderPackedCurrent voteSenderPackedWord
    Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  simp [initState, storageStore_accountMap]

theorem voteFinalState_acc_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    (cA, voteSuccessMap σ I) =
      ((voteFinalState (initState cA gh bl σ σ₀ g A I) I).createdAccounts,
        (voteFinalState (initState cA gh bl σ σ₀ g A I) I).accountMap) := by
  simp [voteFinalState, voteAfterVoteState, voteAfterVotedState, voteSuccessMap,
    voteAfterVoteMap, voteAfterVotedMap, voteUpdatedProposalCount,
    voteUpdatedProposalCountCurrent, voteProposalCountWord, voteProposalCountCurrent,
    voteSenderWeightWord, voteSenderWeightCurrent, voteSenderVotedStoreWord,
    voteSenderVotedStoreCurrent, voteSenderPackedWord, voteSenderPackedCurrent, initState,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    storageStore_createdAccounts, storageStore_accountMap]

/-- The vote success post-state is the same on both sides up to `EVMStateEquiv`: the three
    `SSTORE`s (packed `voted`, `vote` slot, proposal `voteCount`) preserve the simulation relation,
    with the value-level agreements for the two `σ`-dependent writes coming from the chain's own
    `storageLoad` agreement.  This is the multi-write analogue of the Transfer chain. -/
theorem voteFinalState_EVMStateEquiv {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (voteFinalState (initState cA gh bl σ_evm σ₀ g A I) I)
      (voteFinalState (initState cA gh bl σ_solm σ₀ g A I) I) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := EVMStateEquiv.initState hAccounts
  have hVoted : voteSenderVotedStoreCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      voteSenderVotedStoreCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold voteSenderVotedStoreCurrent voteSenderPackedCurrent
    rw [hσ.storageLoad_codeOwner (voteSenderPackedSlot I)]
  have hσVoted : EVMStateEquiv (voteAfterVotedState (initState cA gh bl σ_evm σ₀ g A I) I)
      (voteAfterVotedState (initState cA gh bl σ_solm σ₀ g A I) I) := by
    unfold voteAfterVotedState
    exact hσ.storageStore_codeOwner (voteSenderPackedSlot I) hVoted
  have hσVote : EVMStateEquiv (voteAfterVoteState (initState cA gh bl σ_evm σ₀ g A I) I)
      (voteAfterVoteState (initState cA gh bl σ_solm σ₀ g A I) I) := by
    unfold voteAfterVoteState
    exact hσVoted.storageStore_codeOwner (voteSenderVoteSlot I) rfl
  have hUpdated : voteUpdatedProposalCountCurrent (initState cA gh bl σ_evm σ₀ g A I) I =
      voteUpdatedProposalCountCurrent (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold voteUpdatedProposalCountCurrent voteProposalCountCurrent voteSenderWeightCurrent
    rw [hσVote.storageLoad_codeOwner (voteProposalCountSlot I),
      hσVote.storageLoad_codeOwner (voteSenderSlot I)]
  unfold voteFinalState
  exact hσVote.storageStore_codeOwner (voteProposalCountSlot I) hUpdated

/-! ## Dispatch/decode glue -/

theorem ballotVoteSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_vote {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some voteTransition := by
  refine dispatchMsg_eq_some_of_split (pre := []) (post := [proposalsGetter,
      chairpersonGetter, delegateTransition, winningProposalTransition, giveRightToVoteTransition,
      votersGetter, winnerNameTransition])
    rfl rfl ?_ (by rw [selectorOf, ballotVoteSelectorBytes]; exact hsel)
  intro t ht
  cases ht

theorem ballotVoteBodyCore_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ballotVoteSelector_size hsel
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_none_short (I := I) hshort
  exact (ballotVoteX_decodeRevert_short (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hd hdec

theorem ballotVoteBodyCore_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hbigge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_none_huge (I := I) hbigge
  exact (ballotVoteX_decodeRevert_huge (g := Sat256.ofUInt256 g)
      hsize hbigge hreach)
    |>.reEquivDecodingFailed hcode hd hdec

theorem ballotVoteBodyCore_weight
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ_evm I = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_ok (I := I) hsz36 hbig
  have hbody := ballotVoteBodyReverts_weight
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      rw [voteSenderWeightCurrent_init]
      exact (by simpa [← voteSenderWeightWord_accountMapEquiv hAccounts] using hweight))
  exact (ballotVoteX_weightRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hweight hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotVoteBodyCore_success
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ_evm I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat <
        (voteProposalsLengthWord (voteAfterVoteMap σ_evm I) I).toNat)
    (hfit :
      (voteProposalCountWord (voteAfterVoteMap σ_evm I) I).toNat +
          (voteSenderWeightWord (voteAfterVoteMap σ_evm I) I).toNat <
        UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_ok (I := I) hsz36 hbig
  have hbody := ballotVoteBodyReturns
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      rw [voteSenderWeightCurrent_init]
      exact (by simpa [← voteSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [voteSenderVotedByteCurrent_init]
      exact (by simpa [← voteSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    (by
      rw [voteProposalsLengthCurrent_afterVoteState_init]
      have hmaps := voteAfterVoteMap_accountMapEquiv (I := I) hAccounts
      simpa [← voteProposalsLengthWord_accountMapEquiv hmaps] using hbound)
    (by
      rw [voteProposalCountCurrent_afterVoteState_init,
        voteSenderWeightCurrent_afterVoteState_init]
      have hmaps := voteAfterVoteMap_accountMapEquiv (I := I) hAccounts
      simpa [← voteProposalCountWord_accountMapEquiv hmaps,
        ← voteSenderWeightWord_accountMapEquiv hmaps] using hfit)
  have hacc := voteFinalState_acc_init
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
  exact (ballotVoteX_success (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hweight hvoted hbound hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
      (congrArg Prod.fst hacc)
      (accountMapEquiv.of_eq (congrArg Prod.snd hacc))
      (voteFinalState_EVMStateEquiv (cA := cA) (gh := gh) (bl := bl)
        (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hAccounts)
      (returnEquiv.fallthrough rfl rfl (by decide +native))

theorem ballotVoteBodyCore_overflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ_evm I = ⟨0⟩)
    (hbound :
      (voteProposalWord I).toNat <
        (voteProposalsLengthWord (voteAfterVoteMap σ_evm I) I).toNat)
    (hover : UInt256.size ≤
      (voteProposalCountWord (voteAfterVoteMap σ_evm I) I).toNat +
        (voteSenderWeightWord (voteAfterVoteMap σ_evm I) I).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_ok (I := I) hsz36 hbig
  have hbody := ballotVoteBodyReverts_overflow
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      rw [voteSenderWeightCurrent_init]
      exact (by simpa [← voteSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [voteSenderVotedByteCurrent_init]
      exact (by simpa [← voteSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    (by
      rw [voteProposalsLengthCurrent_afterVoteState_init]
      have hmaps := voteAfterVoteMap_accountMapEquiv (I := I) hAccounts
      simpa [← voteProposalsLengthWord_accountMapEquiv hmaps] using hbound)
    (by
      rw [voteProposalCountCurrent_afterVoteState_init,
        voteSenderWeightCurrent_afterVoteState_init]
      have hmaps := voteAfterVoteMap_accountMapEquiv (I := I) hAccounts
      simpa [← voteProposalCountWord_accountMapEquiv hmaps,
        ← voteSenderWeightWord_accountMapEquiv hmaps] using hover)
  exact (ballotVoteX_overflow (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hweight hvoted hbound hover hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotVoteBodyCore_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ_evm I = ⟨0⟩)
    (hbound :
      ¬ (voteProposalWord I).toNat <
        (voteProposalsLengthWord (voteAfterVoteMap σ_evm I) I).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_ok (I := I) hsz36 hbig
  have hbody := ballotVoteBodyReverts_oob
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      rw [voteSenderWeightCurrent_init]
      exact (by simpa [← voteSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [voteSenderVotedByteCurrent_init]
      exact (by simpa [← voteSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
    (by
      rw [voteProposalsLengthCurrent_afterVoteState_init]
      have hmaps := voteAfterVoteMap_accountMapEquiv (I := I) hAccounts
      simpa [← voteProposalsLengthWord_accountMapEquiv hmaps] using hbound)
  exact (ballotVoteX_oob (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hperm hweight hvoted hbound hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotVoteBodyCore_voted
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hweight : voteSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : voteSenderVotedByte σ_evm I ≠ ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_vote (cd := I.calldata) hsel
  have hdec := ballotDecode_vote_ok (I := I) hsz36 hbig
  have hbody := ballotVoteBodyReverts_voted
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    (by
      rw [voteSenderWeightCurrent_init]
      exact (by simpa [← voteSenderWeightWord_accountMapEquiv hAccounts] using hweight))
    (by
      rw [voteSenderVotedByteCurrent_init]
      exact (by simpa [← voteSenderVotedByte_accountMapEquiv hAccounts] using hvoted))
  exact (ballotVoteX_votedRevert (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hweight hvoted hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotVoteBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x21, 0xb9, 0x3f]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hweight : voteSenderWeightWord σ_evm I = ⟨0⟩
      · exact ballotVoteBodyCore_weight hcode hsize hwv hsel hreach hsz36 hbig hweight
          hAccounts
      · by_cases hvoted : voteSenderVotedByte σ_evm I = ⟨0⟩
        · by_cases hbound :
            (voteProposalWord I).toNat <
              (voteProposalsLengthWord (voteAfterVoteMap σ_evm I) I).toNat
          · by_cases hfit :
              (voteProposalCountWord (voteAfterVoteMap σ_evm I) I).toNat +
                  (voteSenderWeightWord (voteAfterVoteMap σ_evm I) I).toNat <
                UInt256.size
            · exact ballotVoteBodyCore_success hcode hsize hperm hwv hsel hreach hsz36 hbig
                hweight hvoted hbound hfit hAccounts
            · have hover :
                UInt256.size ≤
                  (voteProposalCountWord (voteAfterVoteMap σ_evm I) I).toNat +
                    (voteSenderWeightWord (voteAfterVoteMap σ_evm I) I).toNat := by
                omega
              exact ballotVoteBodyCore_overflow hcode hsize hperm hwv hsel hreach hsz36 hbig
                hweight hvoted hbound hover hAccounts
          · exact ballotVoteBodyCore_oob hcode hsize hperm hwv hsel hreach hsz36 hbig hweight
              hvoted hbound hAccounts
        · exact ballotVoteBodyCore_voted hcode hsize hwv hsel hreach hsz36 hbig hweight hvoted
            hAccounts
    · exact ballotVoteBodyCore_huge hcode hsize hsel hreach (by omega)
  · have hshort : I.calldata.size < 36 := by omega
    exact ballotVoteBodyCore_short hcode hsize hsel hreach hshort

end Ballot
