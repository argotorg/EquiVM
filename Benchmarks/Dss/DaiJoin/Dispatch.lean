import Benchmarks.Dss.DaiJoin.Trusted

/-!
# MakerDAO/Sky DSS DaiJoin dispatcher facts

Solm dispatch routing facts and shared dispatcher-level proof obligations.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

attribute [local simp]
  cageSelectorBytes
  daiSelectorBytes
  denySelectorBytes
  exitSelectorBytes
  joinSelectorBytes
  liveSelectorBytes
  relySelectorBytes
  vatSelectorBytes
  wardsSelectorBytes

theorem daiJoinDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 0)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchDai {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 1)) :
    dispatchMsg contract I.calldata = some daiTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some daiTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 2)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchExit {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 3)) :
    dispatchMsg contract I.calldata = some exitTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some exitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchJoin {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 4)) :
    dispatchMsg contract I.calldata = some joinTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some joinTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 5)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 6)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 7)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (daiJoinSelBytes 8)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = daiJoinSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiJoinDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [cageTransition, daiTransition, denyTransition, exitTransition, joinTransition,
      liveTransition, relyTransition, vatTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, cageSelectorBytes, daiSelectorBytes, denySelectorBytes,
        exitSelectorBytes, joinSelectorBytes, liveSelectorBytes, relySelectorBytes,
        vatSelectorBytes, wardsSelectorBytes]
      native_decide) h

theorem daiJoinDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 9 → (daiJoinSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, cageSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, daiSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [daiJoinSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, exitSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, joinSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [daiJoinSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [daiJoinSelBytes] using hnm 8 (by omega)

theorem daiJoinNoSelectorMatches {I : ExecutionEnv}
    (hcage : ¬ selIs I (daiJoinSelBytes 0))
    (hdai : ¬ selIs I (daiJoinSelBytes 1))
    (hdeny : ¬ selIs I (daiJoinSelBytes 2))
    (hexit : ¬ selIs I (daiJoinSelBytes 3))
    (hjoin : ¬ selIs I (daiJoinSelBytes 4))
    (hlive : ¬ selIs I (daiJoinSelBytes 5))
    (hrely : ¬ selIs I (daiJoinSelBytes 6))
    (hvat : ¬ selIs I (daiJoinSelBytes 7))
    (hwards : ¬ selIs I (daiJoinSelBytes 8)) :
    ∀ i, i < 9 → (daiJoinSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, daiJoinSelBytes] using hcage
  · simpa [selIs, daiJoinSelBytes] using hdai
  · simpa [selIs, daiJoinSelBytes] using hdeny
  · simpa [selIs, daiJoinSelBytes] using hexit
  · simpa [selIs, daiJoinSelBytes] using hjoin
  · simpa [selIs, daiJoinSelBytes] using hlive
  · simpa [selIs, daiJoinSelBytes] using hrely
  · simpa [selIs, daiJoinSelBytes] using hvat
  · simpa [selIs, daiJoinSelBytes] using hwards

theorem daiJoinBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Runtime dispatcher PCs and selector arms -/

abbrev daiJoinRootSplitPc : UInt256 := ⟨32⟩
abbrev daiJoinHighFirstArmPc : UInt256 := ⟨43⟩
abbrev daiJoinLowJumpdestPc : UInt256 := ⟨102⟩
abbrev daiJoinLowFirstArmPc : UInt256 := ⟨103⟩
abbrev daiJoinDispatchBodyPc : UInt256 := ⟨18⟩
abbrev daiJoinSelectorLoadPc : UInt256 := ⟨26⟩
abbrev daiJoinDispatchRevertPc : UInt256 := ⟨147⟩

def daiJoinLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 1 => ⟨#[0x3b, 0x4d, 0xa6, 0x9f]⟩ -- join(address,uint256)
  | 2 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | _ => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()

def daiJoinHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 2 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 3 => ⟨#[0xef, 0x69, 0x3b, 0xed]⟩ -- exit(address,uint256)
  | _ => ⟨#[0xf4, 0xb9, 0xfa, 0x75]⟩ -- dai()

theorem daiJoinSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    daiJoinSelWord I = sel := by
  simpa [daiJoinSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem daiJoinRootSplitWellFormed :
    selectorSplitWellFormed daiJoinBytecode daiJoinRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem daiJoinLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed daiJoinBytecode
      (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem daiJoinHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed daiJoinBytecode
      (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem daiJoinLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) =
      if (daiJoinLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem daiJoinHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) =
      if (daiJoinHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem daiJoinReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiJoinRootSplitPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [daiJoinRootSplitPc, daiJoinSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := daiJoinBytecode)
      (bodyPc := daiJoinDispatchBodyPc) (loadPc := daiJoinSelectorLoadPc)
      (firstPc := daiJoinRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := daiJoinDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem daiJoinReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiJoinLowFirstArmPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiJoinReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h102 : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiJoinLowJumpdestPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiJoinRootSplitPc, daiJoinLowJumpdestPc] using
      RD.selectorSplitTakenAuto h32 daiJoinRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h103 : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiJoinLowFirstArmPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [daiJoinLowFirstArmPc] using h102.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h103⟩

theorem daiJoinReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiJoinHighFirstArmPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiJoinReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiJoinHighFirstArmPc [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiJoinHighFirstArmPc, daiJoinRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 daiJoinRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem daiJoinReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc i))
        (daiJoinSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiJoinBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiJoinReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiJoinLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem daiJoinReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc i))
        (daiJoinSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiJoinBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiJoinReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiJoinHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem daiJoinJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode daiJoinBytecode pc = some (.Push .PUSH2, some (daiJoinDispatchRevertPc, 2)))
    (hjump : decode daiJoinBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h147 := h.push2 daiJoinDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h147 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem daiJoinLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I) daiJoinLowFirstArmPc
      [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h147 := h
    |>.selectorArmNotTakenAuto (daiJoinLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h147 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem daiJoinHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I) daiJoinHighFirstArmPc
      [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h98 := h
    |>.selectorArmNotTakenAuto (daiJoinHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (daiJoinHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact daiJoinJumpToNoMatchRevert h98 (by native_decide) (by native_decide)

theorem daiJoinX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem daiJoinX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt daiJoinBytecode)
    (opC := solcGuardTgtOp daiJoinBytecode)
    (wC := solcGuardTgtWidth daiJoinBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h147 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 daiJoinDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h147 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem daiJoinX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 9 → (daiJoinSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [daiJoinLowArmEq I hsz 0 (by omega)]
      have hfalse : (daiJoinLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinLowSelBytes, daiJoinSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinLowArmEq I hsz 1 (by omega)]
      have hfalse : (daiJoinLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinLowSelBytes, daiJoinSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinLowArmEq I hsz 2 (by omega)]
      have hfalse : (daiJoinLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinLowSelBytes, daiJoinSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinLowArmEq I hsz 3 (by omega)]
      have hfalse : (daiJoinLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinLowSelBytes, daiJoinSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  have heqHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [daiJoinHighArmEq I hsz 0 (by omega)]
      have hfalse : (daiJoinHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinHighSelBytes, daiJoinSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinHighArmEq I hsz 1 (by omega)]
      have hfalse : (daiJoinHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinHighSelBytes, daiJoinSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinHighArmEq I hsz 2 (by omega)]
      have hfalse : (daiJoinHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinHighSelBytes, daiJoinSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinHighArmEq I hsz 3 (by omega)]
      have hfalse : (daiJoinHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinHighSelBytes, daiJoinSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [daiJoinHighArmEq I hsz 4 (by omega)]
      have hfalse : (daiJoinHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [daiJoinHighSelBytes, daiJoinSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) ≠ ⟨0⟩
  · obtain ⟨_, _, hfirst⟩ :=
      daiJoinReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
    exact daiJoinLowNoMatchRevert hfirst heqLow
  · have hroot0 : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    obtain ⟨_, _, hfirst⟩ :=
      daiJoinReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0
    exact daiJoinHighNoMatchRevert hfirst heqHigh

theorem daiJoinNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (daiJoinX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (daiJoinBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem daiJoinNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 9 → (daiJoinSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (daiJoinX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (daiJoinDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (daiJoinX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (daiJoinDispatch_none_short hshort)

end Benchmarks.Dss.DaiJoin
