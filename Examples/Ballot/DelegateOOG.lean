import Examples.Ballot.DelegateChain

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Reasoning.Reach

/-! ## Local cost monotonicity helper -/

/-- Local wrapper for `RD.sload` that preserves the consumed-cost lower bound. -/
theorem RD.sloadMono {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.SLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C',
      C ≤ C' ∧
        RD code ee g s0 (pc + ⟨1⟩)
          ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD a ⟨0⟩)) :: t)
          mem aw rdata (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact ⟨k, C, le_rfl, Or.inl hoog⟩
  · have st := sload_xstep hcode hpc hdec hstk hov
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hco : s.executionEnv.codeOwner = ee.codeOwner := by rw [hee]
    by_cases gg : g.toNat < C + Csload (a :: t) s.substate s.executionEnv
    · exact ⟨k, C, le_rfl, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · refine ⟨k + 1, C + Csload (a :: t) s.substate s.executionEnv, ?_, Or.inr ?_⟩
      · omega
      · refine ⟨stSload s a t,
          hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [stSload]; exact hcode
        · simp only [stSload]; rw [hpc]
        · simp only [stSload]; rw [hσ, hco]
        · simp only [stSload]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
        · have : 1 ≤ Csload (a :: t) s.substate s.executionEnv := by
            unfold Csload
            split <;> decide
          omega
        · simp only [stSload]; exact hmem
        · simp only [stSload]; exact haw
        · simp only [stSload]; exact hrdata
        · simp only [stSload]; rw [hcA, hσ]
        · simp only [stSload]; exact hee
        · simp only [stSload]; exact hworld

end Reasoning.Reach

namespace Ballot

/-! ## Nonterminal delegate-chain out-of-gas branch -/

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopContinueFrom972CurrentCost {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel old w : UInt256} {k C : ℕ}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hnotSender : delegateVoterDelegateWord σ I w ≠ delegateSourceWord I)
    (hreach : RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I old) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      C + 1 ≤ C' ∧
        RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
          [delegateSenderSlot I, delegateVoterDelegateWord σ I w, ⟨156⟩, sel]
          (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd973 := evm_run hreach with [jumpdest]
  have rd987 := evm_run rd973 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
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
  obtain ⟨k1002₀, C1002₀, hC1002₀, rd1002₀⟩ :=
    rd995.sloadMono (by decide) (by evm_ov)
  obtain ⟨k1002, C1002, hC1002, rd1002⟩ : ∃ k' C',
      C + 1 ≤ C' ∧
        RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
          [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
          (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    refine ⟨k1002₀, C1002₀, ?_, ?_⟩
    · omega
    · unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀
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
  obtain ⟨k1042₀, C1042₀, hC1042₀, rd1042₀⟩ :=
    rd1041.sloadMono (by decide) (by evm_ov)
  obtain ⟨k1042, C1042, hC1042, rd1042⟩ : ∃ k' C',
      C + 1 ≤ C' ∧
        RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1042⟩
          [delegateVoterPackedWord σ I w, delegateSenderSlot I, solcAddrMask, ⟨156⟩, sel]
          (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    refine ⟨k1042₀, C1042₀, ?_, ?_⟩
    · omega
    · unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, initState, u256_add_comm]
        using rd1042₀
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
  exact ⟨_,
    C1042 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 10 + 1 + 3 + 8,
    by omega, by
    simpa [delegateVoterDelegateWord,
      u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
      using rd972next⟩

theorem ballotDelegateChainReachHeaderStepsFromFirstCost {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} (n : Nat)
    (hcontinue : ∀ i, 1 ≤ i → i < 1 + n → delegateChainContinuesAt σ I i)
    (hreach : RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      (delegateChainStack σ I sel 1) (delegateChainHeaderMem σ I 1)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      C + n ≤ C' ∧
        RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
          (delegateChainStack σ I sel (1 + n)) (delegateChainHeaderMem σ I (1 + n))
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  induction n generalizing k C with
  | zero =>
    exact ⟨k, C, by omega, by simpa using hreach⟩
  | succ n ih =>
    have hcontinuePrev : ∀ i, 1 ≤ i → i < 1 + n → delegateChainContinuesAt σ I i := by
      intro i hi hlt
      exact hcontinue i hi (by omega)
    obtain ⟨kn, Cn, hCn, hrdn⟩ := ih hcontinuePrev hreach
    have hstepContinue : delegateChainContinuesAt σ I (1 + n) :=
      hcontinue (1 + n) (by omega) (by omega)
    obtain ⟨hnext, hnotSender⟩ := hstepContinue
    obtain ⟨k', C', hC', hrd'⟩ :=
      ballotDelegateX_loopContinueFrom972CurrentCost (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
        (old := delegateChainPrev σ I (1 + n)) (w := delegateChainWord σ I (1 + n))
        (delegateChainWord_canonical_of_pos σ I (by omega))
        (by simpa [delegateChainContinuesAt] using hnext)
        (by simpa [delegateChainContinuesAt] using hnotSender)
        (by
          simpa [delegateChainStack, delegateChainHeaderMem] using hrdn)
    refine ⟨k', C', ?_, ?_⟩
    · omega
    · simpa [delegateChainStack, delegateChainHeaderMem, delegateChainPrev_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrd'

theorem ballotDelegateChainOOGFrom972First {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hcontinue : ∀ i, 1 ≤ i → i ≤ g.toNat + 1 → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      (delegateChainStack σ I sel 1) (delegateChainHeaderMem σ I 1)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    X (g.toNat + 1) (D_J ballotBytecode 0) (initState cA gh bl σ σ₀ g A I) =
      .error .OutOfGass := by
  obtain ⟨k0, C0, hrd0⟩ := hreach
  obtain ⟨k', C', hC', hrd'⟩ :=
    ballotDelegateChainReachHeaderStepsFromFirstCost (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (k := k0) (C := C0) (g.toNat + 1)
      (by
        intro i hi hlt
        exact hcontinue i hi (by omega))
      hrd0
  exact RD.oog_of_cost_gt hrd' (by omega)

theorem ballotDelegateChainOOGFrom245 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hcontinue : ∀ i, 1 ≤ i → i ≤ g.toNat + 1 → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    X (g.toNat + 1) (D_J ballotBytecode 0) (initState cA gh bl σ σ₀ g A I) =
      .error .OutOfGass := by
  have hfirst := ballotDelegateChainReachFirstFrom245 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hbig hcanon hweight hvoted hnotself hnext0 hcycle0 hreach
  exact ballotDelegateChainOOGFrom972First (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hcontinue hfirst

end Ballot
