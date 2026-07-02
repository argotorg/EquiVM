import Examples.Ballot.DelegateTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## Delegate-chain model after the first non-sender loop iteration -/

/-- The Solidity delegate chain: `0` is the ABI argument, and successors follow
`voters[w].delegate` in the initial account map. -/
noncomputable def delegateChainWord (σ : AccountMap) (I : ExecutionEnv) : Nat → UInt256
  | 0 => delegateToWord I
  | n + 1 => delegateVoterDelegateWord σ I (delegateChainWord σ I n)

/-- Previous chain word, used to describe the scratch memory present at the
loop header for indices after the first iteration. -/
noncomputable def delegateChainPrev (σ : AccountMap) (I : ExecutionEnv) : Nat → UInt256
  | 0 => delegateToWord I
  | n + 1 => delegateChainWord σ I n

@[simp] theorem delegateChainWord_zero (σ : AccountMap) (I : ExecutionEnv) :
    delegateChainWord σ I 0 = delegateToWord I := by
  rfl

@[simp] theorem delegateChainWord_succ (σ : AccountMap) (I : ExecutionEnv) (n : Nat) :
    delegateChainWord σ I (n + 1) =
      delegateVoterDelegateWord σ I (delegateChainWord σ I n) := by
  rfl

@[simp] theorem delegateChainPrev_zero (σ : AccountMap) (I : ExecutionEnv) :
    delegateChainPrev σ I 0 = delegateToWord I := by
  rfl

@[simp] theorem delegateChainPrev_succ (σ : AccountMap) (I : ExecutionEnv) (n : Nat) :
    delegateChainPrev σ I (n + 1) = delegateChainWord σ I n := by
  rfl

theorem delegateChainWord_one (σ : AccountMap) (I : ExecutionEnv) :
    delegateChainWord σ I 1 = delegateVoterDelegateWord σ I (delegateToWord I) := by
  rfl

theorem delegateChainWord_canonical_succ (σ : AccountMap) (I : ExecutionEnv) (n : Nat) :
    (delegateChainWord σ I (n + 1)).toNat < EVM.addressModulus := by
  rw [delegateChainWord_succ]
  exact solcAddrMask_result_canonical
    (UInt256.div (delegateVoterPackedWord σ I (delegateChainWord σ I n)) ⟨256⟩)

theorem delegateChainWord_canonical_of_pos (σ : AccountMap) (I : ExecutionEnv) {n : Nat}
    (hn : 0 < n) :
    (delegateChainWord σ I n).toNat < EVM.addressModulus := by
  cases n with
  | zero => cases hn
  | succ n => exact delegateChainWord_canonical_succ σ I n

def delegateChainContinuesAt (σ : AccountMap) (I : ExecutionEnv) (n : Nat) : Prop :=
  delegateVoterDelegateWord σ I (delegateChainWord σ I n) ≠ ⟨0⟩ ∧
    delegateVoterDelegateWord σ I (delegateChainWord σ I n) ≠ delegateSourceWord I

def delegateChainExitsAt (σ : AccountMap) (I : ExecutionEnv) (n : Nat) : Prop :=
  delegateVoterDelegateWord σ I (delegateChainWord σ I n) = ⟨0⟩

def delegateChainHitsSenderAt (σ : AccountMap) (I : ExecutionEnv) (n : Nat) : Prop :=
  delegateVoterDelegateWord σ I (delegateChainWord σ I n) = delegateSourceWord I

theorem delegateChainWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    ∀ n, delegateChainWord σ I n = delegateChainWord τ I n
  | 0 => rfl
  | n + 1 => by
      rw [delegateChainWord_succ, delegateChainWord_succ,
        ← delegateChainWord_accountMapEquiv hστ n]
      exact delegateVoterDelegateWord_accountMapEquiv hστ (delegateChainWord σ I n)

theorem delegateChainContinuesAt_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) {n : Nat} :
    delegateChainContinuesAt σ I n → delegateChainContinuesAt τ I n := by
  intro h
  have hword := delegateChainWord_accountMapEquiv (I := I) hστ n
  constructor
  · simpa [delegateChainContinuesAt, ← hword,
      ← delegateVoterDelegateWord_accountMapEquiv hστ (delegateChainWord σ I n)] using h.1
  · simpa [delegateChainContinuesAt, ← hword,
      ← delegateVoterDelegateWord_accountMapEquiv hστ (delegateChainWord σ I n)] using h.2

theorem delegateChainHitsSenderAt_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) {n : Nat} :
    delegateChainHitsSenderAt σ I n → delegateChainHitsSenderAt τ I n := by
  intro h
  have hword := delegateChainWord_accountMapEquiv (I := I) hστ n
  simpa [delegateChainHitsSenderAt, ← hword,
    ← delegateVoterDelegateWord_accountMapEquiv hστ (delegateChainWord σ I n)] using h

theorem delegateChainExitsAt_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) {n : Nat} :
    delegateChainExitsAt σ I n → delegateChainExitsAt τ I n := by
  intro h
  have hword := delegateChainWord_accountMapEquiv (I := I) hστ n
  simpa [delegateChainExitsAt, ← hword,
    ← delegateVoterDelegateWord_accountMapEquiv hστ (delegateChainWord σ I n)] using h

theorem delegateChainContinuesAt_zero {σ : AccountMap} {I : ExecutionEnv}
    (hnext : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I) :
    delegateChainContinuesAt σ I 0 := by
  exact ⟨by simpa [delegateChainContinuesAt] using hnext,
    by simpa [delegateChainContinuesAt] using hcycle⟩

/-! ## Source-side delegate-loop locals -/

def delegateLoopLocals (I : ExecutionEnv) (w : UInt256) (L : Store) : Prop :=
  L.get? "to" = some (delegateCurrentToValue w) ∧
    L.get? "sender" = some (.storageRef (delegateSenderRef I) voterStructTy) ∧
    L.get? "voters" = none ∧
    L.get? "proposals" = none

theorem delegateLoopLocals_initial (I : ExecutionEnv) :
    delegateLoopLocals I (delegateToWord I) (delegateWithSenderStore I) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [delegateCurrentToValue, delegateToValue] using delegateWithSenderStore_to I
  · unfold delegateWithSenderStore
    exact store_get_self (delegateStore I) "sender"
      (.storageRef (delegateSenderRef I) voterStructTy)
  · simp [delegateWithSenderStore, delegateStore, Std.HashMap.get?_eq_getElem?]
  · simp [delegateWithSenderStore, delegateStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?]

theorem evalExpr_delegate_loopLocals_to (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L } evm (.var "to") =
      .ok (delegateCurrentToValue w) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (L.get? "to") =
    .ok (delegateCurrentToValue w)
  rw [hL.1]
  rfl

theorem evalStorageRef_delegate_loopLocals_voterField (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (field : Ident)
    (hL : delegateLoopLocals I w L) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := L }
      evm (voterF (.var "to") field) = .ok (delegateCurrentVoterFieldRef w field) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterF,
    evalExpr_delegate_loopLocals_to evm I w L hL, delegateCurrentToValue, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateCurrentVoterFieldRef]

theorem resolveStorageRef_delegate_loopLocals_voterDelegate (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := L }
      evm (voterF (.var "to") "delegate") =
        .ok (delegateCurrentVoterFieldRef w "delegate", .elem .address) := by
  exact resolveStorageRef?_ok
    (hbase := by
      simpa [voterF, delegateLoopLocals] using hL.2.2.1)
    (her := evalStorageRef_delegate_loopLocals_voterField evm I w L "delegate" hL)
    (hty := by
      simp [delegateCurrentVoterFieldRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy, addrSt])

theorem evalExpr_delegate_loopLocals_voter_delegate (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L }
      evm (.storage (voterF (.var "to") "delegate")) =
        .ok (delegateCurrentNextValue evm w) := by
  have hresolve := resolveStorageRef_delegate_loopLocals_voterDelegate evm I w L hL
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "delegate")
          (.elem .address) =
        .ok (delegateCurrentNextValue evm w) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot w, offset := 1, size := 20,
          hbound := _, type := .address }) =
      EvalResult.ok (delegateCurrentNextValue evm w)
    rw [storageLocLoad_address_offset1]
    simp [delegateCurrentNextValue, delegateCurrentVoterDelegateWordCurrent,
      delegateCurrentVoterPackedCurrent]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_loopLocals_done (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L }
      evm (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr) =
        .ok (.bool false) := by
  have hstorage := evalExpr_delegate_loopLocals_voter_delegate evm I w L hL
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hstorage, zeroAddr,
    evalBinaryOp?, hdelegate, addrSt, castValue?]

theorem evalExpr_delegate_loopLocals_continues (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L }
      evm (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr) =
        .ok (.bool true) := by
  have hstorage := evalExpr_delegate_loopLocals_voter_delegate evm I w L hL
  have haddr := delegateCurrentDelegateAddress_ne_zero evm w hdelegate
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hstorage, zeroAddr,
    evalBinaryOp?, haddr, addrSt, castValue?]

theorem assign_delegate_loopLocals_to_next (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := L } evm
      .localVar ({ base := "to" } : StorageRef) (delegateCurrentNextValue evm w) =
        .ok ({ contract := ballotContract, locals := L.insert "to" (delegateCurrentNextValue evm w) },
          evm) := by
  have hget : L["to"]? = some (delegateCurrentToValue w) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hL.1
  simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, hget]

theorem delegateLoopLocals_insert_to_next (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L) :
    delegateLoopLocals I (delegateCurrentVoterDelegateWordCurrent evm w)
      (L.insert "to" (delegateCurrentNextValue evm w)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact store_get_self L "to" (delegateCurrentNextValue evm w)
  · rw [store_get_ne L (delegateCurrentNextValue evm w) (by decide)]
    exact hL.2.1
  · rw [store_get_ne L (delegateCurrentNextValue evm w) (by decide)]
    exact hL.2.2.1
  · rw [store_get_ne L (delegateCurrentNextValue evm w) (by decide)]
    exact hL.2.2.2

theorem evalExpr_delegate_loopLocals_to_ne_sender_true (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) (hsrc : evm.executionEnv.source = I.source)
    (hcanon : w.toNat < EVM.addressModulus) (hnotSender : w ≠ delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L }
      evm (.binary .ne (.var "to") sender) = .ok (.bool true) := by
  have haddr : AccountAddress.ofNat w.toNat ≠ evm.executionEnv.source := by
    intro h
    apply hnotSender
    apply delegateWord_eq_source_of_address_eq_source hcanon
    simpa [hsrc] using h
  have htoExpr := evalExpr_delegate_loopLocals_to evm I w L hL
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := L } evm sender =
        .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simpa [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateCurrentToValue,
    evalBinaryOp?] using haddr

theorem evalExpr_delegate_loopLocals_to_ne_sender_false (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) (hsrc : evm.executionEnv.source = I.source)
    (hSender : w = delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := L }
      evm (.binary .ne (.var "to") sender) = .ok (.bool false) := by
  have haddr : AccountAddress.ofNat w.toNat = evm.executionEnv.source := by
    rw [hSender]
    simpa [hsrc] using delegateSource_ofNat I
  have htoExpr := evalExpr_delegate_loopLocals_to evm I w L hL
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := L } evm sender =
        .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simp [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateCurrentToValue, haddr,
    evalBinaryOp?]

theorem ballotDelegateSolm_loopContinueBodyLocals (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (L : Store) (hL : delegateLoopLocals I w L)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanonNext : (delegateCurrentVoterDelegateWordCurrent evm w).toNat < EVM.addressModulus)
    (hnotSender : delegateCurrentVoterDelegateWordCurrent evm w ≠ delegateSourceWord I) :
    ExecBlock ballotConfig { contract := ballotContract, locals := L } evm
      [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
        .require (.binary .ne (.var "to") sender) ]
      (.ok { contract := ballotContract, locals := L.insert "to" (delegateCurrentNextValue evm w) }
        evm) := by
  let L' := L.insert "to" (delegateCurrentNextValue evm w)
  have hL' : delegateLoopLocals I (delegateCurrentVoterDelegateWordCurrent evm w) L' := by
    simpa [L'] using delegateLoopLocals_insert_to_next evm I w L hL
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_loopLocals_voter_delegate evm I w L hL)
      (assign_delegate_loopLocals_to_next evm I w L hL))
    (ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_delegate_loopLocals_to_ne_sender_true evm I
          (delegateCurrentVoterDelegateWordCurrent evm w) L' hL' hsrc hcanonNext hnotSender))
      ExecBlock.nil)

theorem ballotDelegateSolm_loopRevertSenderLocals (evm : EVM.State)
    (I : ExecutionEnv) (w : UInt256) (L : Store)
    (hL : delegateLoopLocals I w L) (hsrc : evm.executionEnv.source = I.source)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w ≠ ⟨0⟩)
    (_hcanonNext : (delegateCurrentVoterDelegateWordCurrent evm w).toNat < EVM.addressModulus)
    (hSender : delegateCurrentVoterDelegateWordCurrent evm w = delegateSourceWord I) :
    ExecStmt ballotConfig { contract := ballotContract, locals := L } evm
      (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
        [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
          .require (.binary .ne (.var "to") sender) ])
      .reverted := by
  let L' := L.insert "to" (delegateCurrentNextValue evm w)
  have hL' : delegateLoopLocals I (delegateCurrentVoterDelegateWordCurrent evm w) L' := by
    simpa [L'] using delegateLoopLocals_insert_to_next evm I w L hL
  refine ExecStmt.whileRevert (evalExpr_delegate_loopLocals_continues evm I w L hL hdelegate) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_loopLocals_voter_delegate evm I w L hL)
      (assign_delegate_loopLocals_to_next evm I w L hL))
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_delegate_loopLocals_to_ne_sender_false evm I
          (delegateCurrentVoterDelegateWordCurrent evm w) L' hL' hsrc hSender)))

theorem delegateCurrentVoterDelegateWordCurrent_init_word {cA gh bl σ σ₀ A I}
    {g : Sat256} (w : UInt256) :
    delegateCurrentVoterDelegateWordCurrent (initState cA gh bl σ σ₀ g A I) w =
      delegateVoterDelegateWord σ I w := by
  rfl

noncomputable def delegateChainStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256)
    (n : Nat) : List UInt256 :=
  [delegateSenderSlot I, delegateChainWord σ I n, ⟨156⟩, sel]

noncomputable def delegateChainHeaderMem (σ : AccountMap) (I : ExecutionEnv)
    (n : Nat) : ByteArray :=
  delegateCurrentLoopMem I (delegateChainPrev σ I n)

noncomputable def delegateChainExitMem (σ : AccountMap) (I : ExecutionEnv)
    (n : Nat) : ByteArray :=
  delegateCurrentLoopMem I (delegateChainWord σ I n)

theorem ballotDelegateChainReachHeaderFrom972Current {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {target : Nat}
    (htarget : 1 ≤ target)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨972⟩ (delegateChainStack σ I sel 1)
      (delegateChainHeaderMem σ I 1) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      (delegateChainStack σ I sel target) (delegateChainHeaderMem σ I target)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd0⟩ := hreach
  let Inv : Nat → Nat → Prop := fun v i => 1 ≤ i ∧ i + v = target
  have hInvStart : Inv (target - 1) 1 := by
    dsimp [Inv]
    omega
  have hexitStep : ∀ i, Inv 0 i → ∀ k C,
      RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
        (delegateChainStack σ I sel i) (delegateChainHeaderMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
        (delegateChainStack σ I sel i) (delegateChainHeaderMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    intro i _ k C hrd
    exact ⟨k, C, hrd⟩
  have hbodyStep : ∀ v i, Inv (v + 1) i → ∀ k C,
      RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
        (delegateChainStack σ I sel i) (delegateChainHeaderMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C →
      ∃ i' k' C',
        Inv v i' ∧ RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
          (delegateChainStack σ I sel i') (delegateChainHeaderMem σ I i')
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    intro v i hInv k C hrd
    have hiLower : 1 ≤ i := hInv.1
    have hiLt : i < target := by
      dsimp [Inv] at hInv
      omega
    obtain ⟨hnext, hnotSender⟩ := hcontinue i hiLower hiLt
    have hcanon : (delegateChainWord σ I i).toNat < EVM.addressModulus :=
      delegateChainWord_canonical_of_pos σ I (by omega)
    obtain ⟨k', C', hrd'⟩ :=
      ballotDelegateX_loopContinueFrom972Current (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
        (old := delegateChainPrev σ I i) (w := delegateChainWord σ I i)
        hcanon
        (by simpa [delegateChainContinuesAt] using hnext)
        (by simpa [delegateChainContinuesAt] using hnotSender)
        ⟨k, C, by
          simpa [delegateChainStack, delegateChainHeaderMem] using hrd⟩
    refine ⟨i + 1, k', C', ?_, ?_⟩
    · dsimp [Inv] at hInv ⊢
      omega
    · simpa [delegateChainStack, delegateChainHeaderMem, delegateChainPrev_succ] using hrd'
  obtain ⟨i, k', C', hInvFinal, hrdFinal⟩ :=
    RD.whileLoopCarryExit (code := ballotBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty) (acc := (cA, σ))
      ⟨972⟩ ⟨972⟩ Inv (delegateChainStack σ I sel)
      (delegateChainHeaderMem σ I) (fun _ => UInt256.ofNat 3)
      (delegateChainStack σ I sel) (delegateChainHeaderMem σ I)
      (fun _ => UInt256.ofNat 3) hexitStep hbodyStep
      (target - 1) 1 hInvStart k0 C0 rd0
  have hi : i = target := by
    dsimp [Inv] at hInvFinal
    omega
  subst i
  exact ⟨k', C', hrdFinal⟩

theorem ballotDelegateSolm_chainExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {target : Nat}
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hexit : delegateChainExitsAt σ I target)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i) :
    ∃ L,
      ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
        (initState cA gh bl σ σ₀ g A I)
        (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ])
        (.ok { contract := ballotContract, locals := L } (initState cA gh bl σ σ₀ g A I)) ∧
      delegateLoopLocals I (delegateChainWord σ I target) L := by
  let evm := initState cA gh bl σ σ₀ g A I
  let cond : Expr := .binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr
  let body : List Stmt :=
    [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
      .require (.binary .ne (.var "to") sender) ]
  let P : Nat → Store → Prop := fun v L =>
    ∃ i, i + v = target ∧ delegateLoopLocals I (delegateChainWord σ I i) L
  have hfalse : ∀ L, P 0 L →
      evalExpr? ballotConfig { contract := ballotContract, locals := L } evm cond =
        .ok (.bool false) := by
    intro L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiTarget : i = target := by omega
    subst i
    have hdone :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I target) = ⟨0⟩ := by
      simpa [evm, delegateChainExitsAt] using hexit
    simpa [cond] using
      evalExpr_delegate_loopLocals_done evm I (delegateChainWord σ I target) L hL hdone
  have htrue : ∀ v L, P (v + 1) L →
      evalExpr? ballotConfig { contract := ballotContract, locals := L } evm cond =
        .ok (.bool true) := by
    intro v L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiLt : i < target := by omega
    have hnext :
        delegateVoterDelegateWord σ I (delegateChainWord σ I i) ≠ ⟨0⟩ := by
      by_cases hzero : i = 0
      · subst i
        simpa using hnext0
      · have hiLower : 1 ≤ i := by omega
        exact (hcontinue i hiLower hiLt).1
    have hnextCurrent :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) ≠ ⟨0⟩ := by
      simpa [evm] using hnext
    simpa [cond] using
      evalExpr_delegate_loopLocals_continues evm I (delegateChainWord σ I i) L hL
        hnextCurrent
  have hstep : ∀ v L, P (v + 1) L →
      ∃ L',
        ExecBlock ballotConfig { contract := ballotContract, locals := L } evm body
          (.ok { contract := ballotContract, locals := L' } evm) ∧ P v L' := by
    intro v L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiLt : i < target := by omega
    have hnotSender :
        delegateVoterDelegateWord σ I (delegateChainWord σ I i) ≠ delegateSourceWord I := by
      by_cases hzero : i = 0
      · subst i
        simpa using hcycle0
      · have hiLower : 1 ≤ i := by omega
        exact (hcontinue i hiLower hiLt).2
    let L' := L.insert "to" (delegateCurrentNextValue evm (delegateChainWord σ I i))
    have hcur :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) =
          delegateChainWord σ I (i + 1) := by
      simpa [evm] using
        delegateCurrentVoterDelegateWordCurrent_init_word (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (delegateChainWord σ I i)
    have hcanonNext :
        (delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i)).toNat <
          EVM.addressModulus := by
      rw [hcur]
      exact delegateChainWord_canonical_of_pos σ I (by omega)
    have hnotSenderCurrent :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) ≠
          delegateSourceWord I := by
      simpa [hcur] using hnotSender
    refine ⟨L', ?_, ?_⟩
    · simpa [body, L'] using
        ballotDelegateSolm_loopContinueBodyLocals evm I (delegateChainWord σ I i) L hL
          (by simp [evm, initState]) hcanonNext hnotSenderCurrent
    · refine ⟨i + 1, by omega, ?_⟩
      have hLnext := delegateLoopLocals_insert_to_next evm I (delegateChainWord σ I i) L hL
      simpa [L', hcur] using hLnext
  obtain ⟨L, hwhile, hP0⟩ :=
    execWhile_var (cfg := ballotConfig) (C := ballotContract) (evm := evm)
      (cond := cond) (body := body) P hfalse htrue hstep target
      (delegateWithSenderStore I) ⟨0, by simp [P], delegateLoopLocals_initial I⟩
  rcases hP0 with ⟨i, hi, hL⟩
  have hiTarget : i = target := by omega
  subst i
  exact ⟨L, by simpa [evm, cond, body] using hwhile, hL⟩

theorem ballotDelegateSolm_chainSenderRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {target : Nat}
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hhit : delegateChainHitsSenderAt σ I target)
    (hnext : delegateVoterDelegateWord σ I (delegateChainWord σ I target) ≠ ⟨0⟩)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i) :
    ExecStmt ballotConfig { contract := ballotContract, locals := delegateWithSenderStore I }
      (initState cA gh bl σ σ₀ g A I)
      (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
        [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
          .require (.binary .ne (.var "to") sender) ])
      .reverted := by
  let evm := initState cA gh bl σ σ₀ g A I
  let cond : Expr := .binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr
  let body : List Stmt :=
    [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
      .require (.binary .ne (.var "to") sender) ]
  let P : Nat → Store → Prop := fun v L =>
    ∃ i, i + v = target ∧ delegateLoopLocals I (delegateChainWord σ I i) L
  have htrue : ∀ v L, P (v + 1) L →
      evalExpr? ballotConfig { contract := ballotContract, locals := L } evm cond =
        .ok (.bool true) := by
    intro v L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiLt : i < target := by omega
    have hnexti :
        delegateVoterDelegateWord σ I (delegateChainWord σ I i) ≠ ⟨0⟩ := by
      by_cases hzero : i = 0
      · subst i
        simpa using hnext0
      · have hiLower : 1 ≤ i := by omega
        exact (hcontinue i hiLower hiLt).1
    have hnextCurrent :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) ≠ ⟨0⟩ := by
      simpa [evm] using hnexti
    simpa [cond] using
      evalExpr_delegate_loopLocals_continues evm I (delegateChainWord σ I i) L hL
        hnextCurrent
  have hstep : ∀ v L, P (v + 1) L →
      ∃ L',
        ExecBlock ballotConfig { contract := ballotContract, locals := L } evm body
          (.ok { contract := ballotContract, locals := L' } evm) ∧ P v L' := by
    intro v L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiLt : i < target := by omega
    have hnotSender :
        delegateVoterDelegateWord σ I (delegateChainWord σ I i) ≠ delegateSourceWord I := by
      by_cases hzero : i = 0
      · subst i
        simpa using hcycle0
      · have hiLower : 1 ≤ i := by omega
        exact (hcontinue i hiLower hiLt).2
    let L' := L.insert "to" (delegateCurrentNextValue evm (delegateChainWord σ I i))
    have hcur :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) =
          delegateChainWord σ I (i + 1) := by
      simpa [evm] using
        delegateCurrentVoterDelegateWordCurrent_init_word (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (delegateChainWord σ I i)
    have hcanonNext :
        (delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i)).toNat <
          EVM.addressModulus := by
      rw [hcur]
      exact delegateChainWord_canonical_of_pos σ I (by omega)
    have hnotSenderCurrent :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I i) ≠
          delegateSourceWord I := by
      simpa [hcur] using hnotSender
    refine ⟨L', ?_, ?_⟩
    · simpa [body, L'] using
        ballotDelegateSolm_loopContinueBodyLocals evm I (delegateChainWord σ I i) L hL
          (by simp [evm, initState]) hcanonNext hnotSenderCurrent
    · refine ⟨i + 1, by omega, ?_⟩
      have hLnext := delegateLoopLocals_insert_to_next evm I (delegateChainWord σ I i) L hL
      simpa [L', hcur] using hLnext
  have hterminal : ∀ L, P 0 L →
      ExecStmt ballotConfig { contract := ballotContract, locals := L } evm
        (.while cond body) .reverted := by
    intro L hP
    rcases hP with ⟨i, hi, hL⟩
    have hiTarget : i = target := by omega
    subst i
    have hcur :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I target) =
          delegateVoterDelegateWord σ I (delegateChainWord σ I target) := by
      simpa [evm] using
        delegateCurrentVoterDelegateWordCurrent_init_word (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (delegateChainWord σ I target)
    have hnextCurrent :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I target) ≠ ⟨0⟩ := by
      simpa [hcur] using hnext
    have hSender :
        delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I target) =
          delegateSourceWord I := by
      simpa [hcur, delegateChainHitsSenderAt] using hhit
    have hcanonSender :
        (delegateCurrentVoterDelegateWordCurrent evm (delegateChainWord σ I target)).toNat <
          EVM.addressModulus := by
      rw [hSender]
      exact delegateSourceWord_canonical I
    simpa [cond, body] using
      ballotDelegateSolm_loopRevertSenderLocals evm I (delegateChainWord σ I target) L hL
        (by simp [evm, initState]) hnextCurrent hcanonSender hSender
  have hrun : ∀ v L, P v L →
      ExecStmt ballotConfig { contract := ballotContract, locals := L } evm
        (.while cond body) .reverted := by
    intro v
    induction v with
    | zero =>
      intro L hP
      exact hterminal L hP
    | succ v ih =>
      intro L hP
      obtain ⟨L', hbody, hP'⟩ := hstep v L hP
      exact ExecStmt.whileTrue (htrue v L hP) hbody (ih L' hP')
  simpa [evm, cond, body] using
    hrun target (delegateWithSenderStore I)
      ⟨0, by simp [P], delegateLoopLocals_initial I⟩

theorem ballotDelegateChainReachExitFrom972Current {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {target : Nat}
    (htarget : 1 ≤ target)
    (hexit : delegateChainExitsAt σ I target)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨972⟩ (delegateChainStack σ I sel 1)
      (delegateChainHeaderMem σ I 1) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      (delegateChainStack σ I sel target) (delegateChainExitMem σ I target)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd0⟩ := hreach
  let Inv : Nat → Nat → Prop := fun v i => 1 ≤ i ∧ i + v = target
  have hInvStart : Inv (target - 1) 1 := by
    dsimp [Inv]
    omega
  have hexitStep : ∀ i, Inv 0 i → ∀ k C,
      RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
        (delegateChainStack σ I sel i) (delegateChainHeaderMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
        (delegateChainStack σ I sel i) (delegateChainExitMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    intro i hInv k C hrd
    have hi : i = target := by
      dsimp [Inv] at hInv
      omega
    subst i
    exact ballotDelegateX_loopExitFrom972Current (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (old := delegateChainPrev σ I target) (w := delegateChainWord σ I target)
      (delegateChainWord_canonical_of_pos σ I (by omega))
      (by simpa [delegateChainExitsAt] using hexit)
      ⟨k, C, by
        simpa [delegateChainStack, delegateChainHeaderMem, delegateChainExitMem] using hrd⟩
  have hbodyStep : ∀ v i, Inv (v + 1) i → ∀ k C,
      RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
        (delegateChainStack σ I sel i) (delegateChainHeaderMem σ I i)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C →
      ∃ i' k' C',
        Inv v i' ∧ RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
          (delegateChainStack σ I sel i') (delegateChainHeaderMem σ I i')
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    intro v i hInv k C hrd
    have hiLower : 1 ≤ i := hInv.1
    have hiLt : i < target := by
      dsimp [Inv] at hInv
      omega
    obtain ⟨hnext, hnotSender⟩ := hcontinue i hiLower hiLt
    have hcanon : (delegateChainWord σ I i).toNat < EVM.addressModulus :=
      delegateChainWord_canonical_of_pos σ I (by omega)
    obtain ⟨k', C', hrd'⟩ :=
      ballotDelegateX_loopContinueFrom972Current (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
        (old := delegateChainPrev σ I i) (w := delegateChainWord σ I i)
        hcanon
        (by simpa [delegateChainContinuesAt] using hnext)
        (by simpa [delegateChainContinuesAt] using hnotSender)
        ⟨k, C, by
          simpa [delegateChainStack, delegateChainHeaderMem] using hrd⟩
    refine ⟨i + 1, k', C', ?_, ?_⟩
    · dsimp [Inv] at hInv ⊢
      omega
    · simpa [delegateChainStack, delegateChainHeaderMem, delegateChainPrev_succ] using hrd'
  obtain ⟨i, k', C', hInvFinal, hrdFinal⟩ :=
    RD.whileLoopCarryExit (code := ballotBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty) (acc := (cA, σ))
      ⟨972⟩ ⟨1134⟩ Inv (delegateChainStack σ I sel)
      (delegateChainHeaderMem σ I) (fun _ => UInt256.ofNat 3)
      (delegateChainStack σ I sel) (delegateChainExitMem σ I)
      (fun _ => UInt256.ofNat 3) hexitStep hbodyStep
      (target - 1) 1 hInvStart k0 C0 rd0
  have hi : i = target := by
    dsimp [Inv] at hInvFinal
    omega
  subst i
  exact ⟨k', C', hrdFinal⟩

theorem ballotDelegateChainReachFirstFrom245 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      (delegateChainStack σ I sel 1) (delegateChainHeaderMem σ I 1)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := ballotDelegateX_afterNotSelf (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) hsz36 hsize hbig hcanon hweight hvoted hnotself hreach
  obtain ⟨k', C', hrd'⟩ := ballotDelegateX_loopContinueFrom972 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (sel := sel) (w := delegateToWord I) hcanon hnext hcycle ⟨_, _, rd972⟩
  exact ⟨k', C', by
    simpa [delegateChainStack, delegateChainHeaderMem, delegateChainWord_one] using hrd'⟩

theorem ballotDelegateChainReachExitFrom245 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {target : Nat}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (htarget : 1 ≤ target)
    (hexit : delegateChainExitsAt σ I target)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      (delegateChainStack σ I sel target) (delegateChainExitMem σ I target)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hfirst := ballotDelegateChainReachFirstFrom245 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hbig hcanon hweight hvoted hnotself hnext hcycle hreach
  exact ballotDelegateChainReachExitFrom972Current (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (target := target) htarget hexit hcontinue hfirst

theorem ballotDelegateChainSenderRevertFrom972Current {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {target : Nat}
    (htarget : 1 ≤ target)
    (hhit : delegateChainHitsSenderAt σ I target)
    (hnext : delegateVoterDelegateWord σ I (delegateChainWord σ I target) ≠ ⟨0⟩)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨972⟩ (delegateChainStack σ I sel 1)
      (delegateChainHeaderMem σ I 1) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hheader := ballotDelegateChainReachHeaderFrom972Current (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (target := target) htarget hcontinue hreach
  exact ballotDelegateX_loopSenderRevertFrom972Current (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (old := delegateChainPrev σ I target) (w := delegateChainWord σ I target)
    (delegateChainWord_canonical_of_pos σ I (by omega))
    (by simpa using hnext)
    (by simpa [delegateChainHitsSenderAt] using hhit)
    (by
      obtain ⟨k, C, hrd⟩ := hheader
      exact ⟨k, C, by
        simpa [delegateChainStack, delegateChainHeaderMem] using hrd⟩)

theorem ballotDelegateChainSenderRevertFrom245 {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {target : Nat}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (htarget : 1 ≤ target)
    (hhit : delegateChainHitsSenderAt σ I target)
    (hnext : delegateVoterDelegateWord σ I (delegateChainWord σ I target) ≠ ⟨0⟩)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hfirst := ballotDelegateChainReachFirstFrom245 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hbig hcanon hweight hvoted hnotself hnext0 hcycle0 hreach
  exact ballotDelegateChainSenderRevertFrom972Current (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (target := target) htarget hhit hnext hcontinue hfirst

theorem ballotDelegateBodyReverts_chainSender {cA gh bl σ σ₀ A I} {g : Sat256}
    {target : Nat}
    (hwv : I.weiValue = ⟨0⟩)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ I (delegateToWord I) ≠ delegateSourceWord I)
    (hhit : delegateChainHitsSenderAt σ I target)
    (hnext : delegateVoterDelegateWord σ I (delegateChainWord σ I target) ≠ ⟨0⟩)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ I i) :
    ExecTransitionBody ballotConfig ballotContract (initState cA gh bl σ σ₀ g A I)
      (delegateStore I)
      delegateTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (resolveStorageRef_delegate_sender
      (initState cA gh bl σ σ₀ g A I) I (by simp [initState]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_weight_zero_false
      (initState cA gh bl σ σ₀ g A I) I
      (by simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using hweight))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_sender_not_voted_true
      (initState cA gh bl σ σ₀ g A I) I
      (by
        change UInt256.land (delegateSenderPackedWord σ I) ⟨255⟩ = ⟨0⟩
        rw [u256_land_comm (delegateSenderPackedWord σ I) ⟨255⟩]
        exact hvoted))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_delegate_to_ne_sender_true
      (initState cA gh bl σ σ₀ g A I) I (by simp [initState]) hcanon hnotself)) ?_
  exact ExecBlock.consRevert
    (ballotDelegateSolm_chainSenderRevert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (target := target) hnext0 hcycle0 hhit hnext hcontinue)

theorem ballotDelegateChainSenderRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {sel : UInt256} {target : Nat}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext0 : delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle0 : delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ delegateSourceWord I)
    (htarget : 1 ≤ target)
    (hhit : delegateChainHitsSenderAt σ_evm I target)
    (hnext : delegateVoterDelegateWord σ_evm I (delegateChainWord σ_evm I target) ≠ ⟨0⟩)
    (hcontinue : ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ_evm I i)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
    simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
  have hvotedSolm : delegateSenderVotedByte σ_solm I = ⟨0⟩ := by
    simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted
  have hnext0Solm : delegateVoterDelegateWord σ_solm I (delegateToWord I) ≠ ⟨0⟩ := by
    simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
      using hnext0
  have hcycle0Solm :
      delegateVoterDelegateWord σ_solm I (delegateToWord I) ≠ delegateSourceWord I := by
    simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
      using hcycle0
  have hhitSolm : delegateChainHitsSenderAt σ_solm I target :=
    delegateChainHitsSenderAt_accountMapEquiv (I := I) hAccounts hhit
  have hnextSolm :
      delegateVoterDelegateWord σ_solm I (delegateChainWord σ_solm I target) ≠ ⟨0⟩ := by
    have hword := delegateChainWord_accountMapEquiv (I := I) hAccounts target
    simpa [← hword,
      ← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateChainWord σ_evm I target)]
      using hnext
  have hcontinueSolm :
      ∀ i, 1 ≤ i → i < target → delegateChainContinuesAt σ_solm I i := by
    intro i hi hlt
    exact delegateChainContinuesAt_accountMapEquiv (I := I) hAccounts (hcontinue i hi hlt)
  have hbody := ballotDelegateBodyReverts_chainSender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (target := target) hwv hcanon hweightSolm hvotedSolm hnotself hnext0Solm hcycle0Solm
    hhitSolm hnextSolm hcontinueSolm
  exact (ballotDelegateChainSenderRevertFrom245 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (target := target) hsz36 hsize hbig hcanon hweight hvoted hnotself
      hnext0 hcycle0 htarget hhit hnext hcontinue hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

/-
Missing shared source-side lemma proposal (`Reasoning/SolmBody.lean` or a small
`Reasoning/Store.lean`):

  theorem execWhile_var_extensional_locals
      {cfg C evm cond body} (P : Nat → Store → Prop)
      (Final : Store → Store → Prop)
      ... :
      ∀ v L, P v L →
        ∃ L', ExecStmt cfg { contract := C, locals := L } evm (.while cond body)
          (.ok { contract := C, locals := L' } evm) ∧ P 0 L' ∧ Final L' canonical

For Ballot.delegate the concrete needed instance is an extensional bridge:

  theorem delegateCurrentNextStore_equiv_currentWithSenderStore
      (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) :
      storeLookupEquiv (delegateCurrentNextStore evm I w)
        (delegateCurrentWithSenderStore I (delegateCurrentVoterDelegateWordCurrent evm w))

plus tail/source body helpers that consume `storeLookupEquiv` instead of definitional
equality to `delegateCurrentWithSenderStore`.

Missing shared EVM/OOG lemma proposal (`Reasoning/Reach.lean`):

  theorem ballotDelegateX_loopContinueFrom972CurrentCost
      {cA gh bl σ σ₀ A I} {g : Sat256} {sel old w : UInt256} {k C : Nat}
      (hcanon : w.toNat < EVM.addressModulus)
      (hnext : delegateVoterDelegateWord σ I w ≠ 0)
      (hnotSender : delegateVoterDelegateWord σ I w ≠ delegateSourceWord I)
      (hreach : RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) 972
        [delegateSenderSlot I, w, 156, sel] (delegateCurrentLoopMem I old)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      ∃ k' C',
        C + DELEGATE_LOOP_CONTINUE_MIN_COST ≤ C' ∧
        RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) 972
          [delegateSenderSlot I, delegateVoterDelegateWord σ I w, 156, sel]
          (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) k' C'

Then the never-terminal branch iterates that helper `g.toNat + 1` times, obtains
`g.toNat < C'`, and closes directly with the already-shared `RD.oog_of_cost_gt`.
The important extra payload over current recurrent helpers is the monotone consumed
cost lower bound. Current `RD.whileLoop*` existentializes `C'` and is perfect for
finite terminal chains, but it cannot prove the nonterminal chain's inevitable OOG
without preserving this lower bound.
-/

end Ballot
