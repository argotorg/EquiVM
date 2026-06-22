import Examples.Ballot.DelegateTailGeneral
import Examples.Ballot.DelegateOOG

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Ballot

/-! ## Delegate tail wrappers after a finite chain exit -/

theorem ballotDelegateTailWeightRevertEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
    (hdelegateWeight : delegateVoterWeightWord σ I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanonInit
  have hbody := ballotDelegateBodyReverts_tailDelegateWeight_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
  exact (ballotDelegateX_tailDelegateWeightRevertFrom1134 (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hcanonTail hdelegateWeight hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateTailNotVotedSuccessEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
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
  have hbody := ballotDelegateBodyReturns_tailNotVoted_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateNotVoted)
    (by
      rw [delegateTailVoterWeightCurrent_afterSenderState_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hfit)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight
    hreach
  exact (ballotDelegateX_tailNotVotedSuccessFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hperm hdelegateNotVoted hfit hreach1211)
    |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
      (delegateTailFalseSuccessState_created_init (g := Sat256.ofUInt256 g) w)
      (delegateTailFalseSuccessState_accountMapEquiv_init
        (g := Sat256.ofUInt256 g) w hweight hfit)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateTailNotVotedOverflowEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
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
  have hbody := ballotDelegateBodyReverts_tailNotVotedOverflow_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateNotVoted)
    (by
      rw [delegateTailVoterWeightCurrent_afterSenderState_init,
        delegateTailSenderWeightCurrent_afterSenderState_init]
      exact hover)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight
    hreach
  exact (ballotDelegateX_tailNotVotedOverflowFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateNotVoted hover hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateTailVotedSuccessEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
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
  have hbody := ballotDelegateBodyReturns_tailVoted_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
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
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight
    hreach
  exact (ballotDelegateX_tailVotedSuccessFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hperm hdelegateVoted hbound hfit hreach1211)
    |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
      (delegateTailTrueSuccessState_created_init (g := Sat256.ofUInt256 g) w)
      (delegateTailTrueSuccessState_accountMapEquiv_init
        (g := Sat256.ofUInt256 g) w hweight hfit)
      (returnEquiv.void rfl rfl rfl)

theorem ballotDelegateTailVotedOobEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
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
  have hbody := ballotDelegateBodyReverts_tailVotedOob_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
    (by rw [delegateTailVoterWeightCurrent_init]; exact hdelegateWeight)
    (by rw [delegateTailVoterVotedByteCurrent_afterSenderState_init]; exact hdelegateVoted)
    (by
      rw [delegateTailVoterVoteCurrent_afterSenderState_init,
        delegateTailProposalsLengthCurrent_afterSenderState_init]
      exact hbound)
  have hreach1211 := ballotDelegateX_tailAfterSenderPackedStoreFrom1134
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight
    hreach
  exact (ballotDelegateX_tailVotedOobFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateVoted hbound hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateTailVotedOverflowEquiv_general {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel w : UInt256} {L : Store}
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
        (.ok { contract := ballotContract, locals := L }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hL : delegateLoopLocals I w L)
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
  have hbody := ballotDelegateBodyReverts_tailVotedOverflow_general
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I w L hL
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanonInit hcanonTail
    (by rw [delegateSenderWeightCurrent_init]; exact hweight)
    (by rw [delegateSenderVotedByteCurrent_init]; exact hvoted)
    hnotself hwhile
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
    (g := Sat256.ofUInt256 g) (sel := sel) (w := w) hperm hcanonTail hdelegateWeight
    hreach
  exact (ballotDelegateX_tailVotedOverflowFrom1211 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := w) hdelegateVoted hbound hover hreach1211)
    |>.reEquivExecutionRevert hcode hd hdec hbody

/-! ## Complete delegate loop continuation -/

theorem ballotDelegateChainExitEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel : UInt256} {target : Nat}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (htarget : 1 ≤ target)
    (hexit : delegateChainExitsAt σ I target)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  obtain ⟨L, hwhile, hL⟩ := ballotDelegateSolm_chainExit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (target := target) hnext0 hcycle0 hexit hcontinue
  have hreachTail0 := ballotDelegateChainReachExitFrom245 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) (target := target)
    hsz36 hsize hbig hcanon hweight hvoted hnotself hnext0 hcycle0 htarget hexit
    hcontinue hreach
  let w := delegateChainWord σ I target
  have hcanonTail : w.toNat < EVM.addressModulus := by
    dsimp [w]
    exact delegateChainWord_canonical_of_pos σ I (by omega)
  have hreachTail : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [w, delegateChainStack, delegateChainExitMem] using hreachTail0
  by_cases hdelegateWeight : delegateVoterWeightWord σ I w = ⟨0⟩
  · exact ballotDelegateTailWeightRevertEquiv_general hcode hsize hwv hsel hsz36 hbig
      hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight hreachTail
  · by_cases hdelegateNotVoted :
      delegateVoterVotedByte (delegateTailAfterSenderMap σ I w) I w = ⟨0⟩
    · by_cases hfit :
        (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
            (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
          UInt256.size
      · exact ballotDelegateTailNotVotedSuccessEquiv_general hcode hsize hwv hperm hsel
          hsz36 hbig hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight
          hdelegateNotVoted hfit hreachTail
      · have hover :
          UInt256.size ≤
            (delegateVoterWeightWord (delegateTailAfterSenderMap σ I w) I w).toNat +
              (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat := by
          omega
        exact ballotDelegateTailNotVotedOverflowEquiv_general hcode hsize hwv hperm hsel
          hsz36 hbig hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight
          hdelegateNotVoted hover hreachTail
    · by_cases hbound :
        (delegateVoterVoteWord (delegateTailAfterSenderMap σ I w) I w).toNat <
          (delegateTailProposalsLengthWord σ I w).toNat
      · by_cases hfit :
          (delegateTailProposalCountWord σ I w).toNat +
              (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat <
            UInt256.size
        · exact ballotDelegateTailVotedSuccessEquiv_general hcode hsize hwv hperm hsel
            hsz36 hbig hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight
            hdelegateNotVoted hbound hfit hreachTail
        · have hover :
            UInt256.size ≤
              (delegateTailProposalCountWord σ I w).toNat +
                (delegateSenderWeightWord (delegateTailAfterSenderMap σ I w) I).toNat := by
            omega
          exact ballotDelegateTailVotedOverflowEquiv_general hcode hsize hwv hperm hsel
            hsz36 hbig hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight
            hdelegateNotVoted hbound hover hreachTail
      · exact ballotDelegateTailVotedOobEquiv_general hcode hsize hwv hperm hsel
          hsz36 hbig hcanon hcanonTail hweight hvoted hnotself hwhile hL hdelegateWeight
          hdelegateNotVoted hbound hreachTail

theorem ballotDelegateChainOOGEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hcontinue :
      ∀ i, 1 ≤ i → i ≤ (Sat256.ofUInt256 g).toNat + 1 →
        delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hoog := ballotDelegateChainOOGFrom245 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
    hsz36 hsize hbig hcanon hweight hvoted hnotself hnext0 hcycle0 hcontinue hreach
  exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
    rw [← hcode] at hoog
    simpa [initState, Sat256.ofUInt256] using hoog))

theorem ballotDelegateLoopContinuationEquiv {cA gh bl σ σ₀ A I}
    {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  let N := (Sat256.ofUInt256 g).toNat + 1
  by_cases hexit :
      ∃ target,
        1 ≤ target ∧ target ≤ N ∧ delegateChainExitsAt σ I target ∧
          ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i
  · rcases hexit with ⟨target, htarget, _hle, hexitTarget, hcontinue⟩
    exact ballotDelegateChainExitEquiv hcode hsize hwv hperm hsel hsz36 hbig hcanon
      hweight hvoted hnotself hnext0 hcycle0 htarget hexitTarget hcontinue hreach
  · by_cases hhit :
      ∃ target,
        1 ≤ target ∧ target ≤ N ∧ delegateChainHitsSenderAt σ I target ∧
          delegateVoterDelegateWord σ I (delegateChainWord σ I target) ≠ ⟨0⟩ ∧
          ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i
    · rcases hhit with ⟨target, htarget, _hle, hhitTarget, hnextTarget, hcontinue⟩
      exact ballotDelegateChainSenderRevertEquiv hcode hsize hwv hsel hsz36 hbig hcanon
        hweight hvoted hnotself hnext0 hcycle0 htarget hhitTarget hnextTarget hcontinue
        hreach
    · have hcontinueAll :
        ∀ i, 1 ≤ i → i ≤ N → delegateChainContinuesAt σ I i := by
        intro i hi hle
        induction i using Nat.strong_induction_on with
        | h i ih =>
          have hprefix : ∀ j, 1 ≤ j → j < i → delegateChainContinuesAt σ I j := by
            intro j hj hji
            exact ih j hji hj (by omega)
          by_cases hzero :
              delegateVoterDelegateWord σ I (delegateChainWord σ I i) = ⟨0⟩
          · exact False.elim (hexit ⟨i, hi, hle, hzero, hprefix⟩)
          · by_cases hsender :
              delegateVoterDelegateWord σ I (delegateChainWord σ I i) = delegateSourceWord I
            · exact False.elim (hhit ⟨i, hi, hle, hsender, hzero, hprefix⟩)
            · exact ⟨hzero, hsender⟩
      exact ballotDelegateChainOOGEquiv hcode hsize hsz36 hbig hcanon hweight hvoted
        hnotself hnext0 hcycle0 (by simpa [N] using hcontinueAll) hreach

theorem ballotDelegateBodyCoreComplete {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  refine ballotDelegateBodyCoreLoopFrontier hcode hsize hperm hwv hsel hreach ?_
  intro hsz36 hbig hcanon hweight hvoted hnotself hperm hnext0 hcycle0
  exact ballotDelegateLoopContinuationEquiv hcode hsize hwv hperm hsel hsz36 hbig hcanon
    hweight hvoted hnotself hnext0 hcycle0 hreach

end Ballot
