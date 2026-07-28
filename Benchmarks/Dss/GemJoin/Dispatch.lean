import Benchmarks.Dss.GemJoin.Trusted

/-!
# MakerDAO/Sky DSS GemJoin dispatcher scaffold

Solm dispatch routing facts plus the shared runtime-dispatch obligations used by the top-level
correctness theorem. The no-dispatch and non-payable runtime paths are proof leaves for the
scaffold phase and will be discharged before the benchmark is complete.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.GemJoin

attribute [local simp]
  gemJoinCageSelectorBytes
  gemJoinDecSelectorBytes
  gemJoinDenySelectorBytes
  gemJoinExitSelectorBytes
  gemJoinGemSelectorBytes
  gemJoinIlkSelectorBytes
  gemJoinJoinSelectorBytes
  gemJoinLiveSelectorBytes
  gemJoinRelySelectorBytes
  gemJoinVatSelectorBytes
  gemJoinWardsSelectorBytes

theorem gemJoinDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 0)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchDec {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 1)) :
    dispatchMsg contract I.calldata = some decTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some decTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 2)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchExit {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 3)) :
    dispatchMsg contract I.calldata = some exitTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some exitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchGem {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 4)) :
    dispatchMsg contract I.calldata = some gemTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gemTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchIlk {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 5)) :
    dispatchMsg contract I.calldata = some ilkTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ilkTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchJoin {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 6)) :
    dispatchMsg contract I.calldata = some joinTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some joinTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 7)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 8)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 9)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (gemJoinSelBytes 10)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = gemJoinSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem gemJoinNoSelectorMatches {I : ExecutionEnv}
    (hcage : ¬ selIs I (gemJoinSelBytes 0))
    (hdec : ¬ selIs I (gemJoinSelBytes 1))
    (hdeny : ¬ selIs I (gemJoinSelBytes 2))
    (hexit : ¬ selIs I (gemJoinSelBytes 3))
    (hgem : ¬ selIs I (gemJoinSelBytes 4))
    (hilk : ¬ selIs I (gemJoinSelBytes 5))
    (hjoin : ¬ selIs I (gemJoinSelBytes 6))
    (hlive : ¬ selIs I (gemJoinSelBytes 7))
    (hrely : ¬ selIs I (gemJoinSelBytes 8))
    (hvat : ¬ selIs I (gemJoinSelBytes 9))
    (hwards : ¬ selIs I (gemJoinSelBytes 10)) :
    ∀ i, i < 11 → (gemJoinSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, gemJoinSelBytes] using hcage
  · simpa [selIs, gemJoinSelBytes] using hdec
  · simpa [selIs, gemJoinSelBytes] using hdeny
  · simpa [selIs, gemJoinSelBytes] using hexit
  · simpa [selIs, gemJoinSelBytes] using hgem
  · simpa [selIs, gemJoinSelBytes] using hilk
  · simpa [selIs, gemJoinSelBytes] using hjoin
  · simpa [selIs, gemJoinSelBytes] using hlive
  · simpa [selIs, gemJoinSelBytes] using hrely
  · simpa [selIs, gemJoinSelBytes] using hvat
  · simpa [selIs, gemJoinSelBytes] using hwards

theorem gemJoinDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [cageTransition, decTransition, denyTransition, exitTransition, gemTransition, ilkTransition,
      joinTransition, liveTransition, relyTransition, vatTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, gemJoinCageSelectorBytes, gemJoinDecSelectorBytes,
        gemJoinDenySelectorBytes, gemJoinExitSelectorBytes, gemJoinGemSelectorBytes,
        gemJoinIlkSelectorBytes, gemJoinJoinSelectorBytes, gemJoinLiveSelectorBytes,
        gemJoinRelySelectorBytes, gemJoinVatSelectorBytes, gemJoinWardsSelectorBytes,
        gemJoinSelBytes]
      native_decide) h

theorem gemJoinDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 11 → (gemJoinSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, gemJoinCageSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, gemJoinDecSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, gemJoinDenySelectorBytes]
    simpa [gemJoinSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, gemJoinExitSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, gemJoinGemSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, gemJoinIlkSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, gemJoinJoinSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, gemJoinLiveSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, gemJoinRelySelectorBytes]
    simpa [gemJoinSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, gemJoinVatSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, gemJoinWardsSelectorBytes]
    simpa [gemJoinSelBytes] using hnm 10 (by omega)

/-! ## Runtime dispatcher PCs and selector arms -/

abbrev gemJoinRootSplitPc : UInt256 := ⟨32⟩
abbrev gemJoinHighFirstArmPc : UInt256 := ⟨43⟩
abbrev gemJoinLowJumpdestPc : UInt256 := ⟨113⟩
abbrev gemJoinLowFirstArmPc : UInt256 := ⟨114⟩
abbrev gemJoinDispatchBodyPc : UInt256 := ⟨18⟩
abbrev gemJoinSelectorLoadPc : UInt256 := ⟨26⟩
abbrev gemJoinDispatchRevertPc : UInt256 := ⟨169⟩

def gemJoinLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 1 => ⟨#[0x3b, 0x4d, 0xa6, 0x9f]⟩ -- join(address,uint256)
  | 2 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | _ => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ -- gem()

def gemJoinHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 2 => ⟨#[0xb3, 0xbc, 0xfa, 0x82]⟩ -- dec()
  | 3 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 4 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩ -- ilk()
  | _ => ⟨#[0xef, 0x69, 0x3b, 0xed]⟩ -- exit(address,uint256)

theorem gemJoinSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    gemJoinSelWord I = sel := by
  simpa [gemJoinSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem gemJoinBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem gemJoinRootSplitWellFormed :
    selectorSplitWellFormed gemJoinBytecode gemJoinRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem gemJoinLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed gemJoinBytecode
      (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem gemJoinHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed gemJoinBytecode
      (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem gemJoinLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) =
      if (gemJoinLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem gemJoinHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) =
      if (gemJoinHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem gemJoinReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        gemJoinRootSplitPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [gemJoinRootSplitPc, gemJoinSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := gemJoinBytecode)
      (bodyPc := gemJoinDispatchBodyPc) (loadPc := gemJoinSelectorLoadPc)
      (firstPc := gemJoinRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := gemJoinDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem gemJoinReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I)
      ≠ ⟨0⟩) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        gemJoinLowFirstArmPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    gemJoinReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h113 : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      gemJoinLowJumpdestPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [gemJoinRootSplitPc, gemJoinLowJumpdestPc] using
      RD.selectorSplitTakenAuto h32 gemJoinRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h114 : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      gemJoinLowFirstArmPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [gemJoinLowFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem gemJoinReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I)
      = ⟨0⟩) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        gemJoinHighFirstArmPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    gemJoinReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
      gemJoinHighFirstArmPc [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [gemJoinHighFirstArmPc, gemJoinRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 gemJoinRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem gemJoinReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I)
      ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc i))
        (gemJoinSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J gemJoinBytecode 0).contains bodyPC = true)
    (hbody : armTgt gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    gemJoinReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => gemJoinLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem gemJoinReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I)
      = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc i))
        (gemJoinSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J gemJoinBytecode 0).contains bodyPC = true)
    (hbody : armTgt gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    gemJoinReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => gemJoinHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem gemJoinJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode gemJoinBytecode pc = some (.Push .PUSH2, some (gemJoinDispatchRevertPc, 2)))
    (hjump : decode gemJoinBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h.push2 gemJoinDispatchRevertPc hpush
      (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h169 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem gemJoinLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) gemJoinLowFirstArmPc
      [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h
    |>.selectorArmNotTakenAuto (gemJoinLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h169 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem gemJoinHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) gemJoinHighFirstArmPc
      [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (gemJoinHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact gemJoinJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem gemJoinX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem gemJoinX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt gemJoinBytecode)
    (opC := solcGuardTgtOp gemJoinBytecode)
    (wC := solcGuardTgtWidth gemJoinBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h169 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 gemJoinDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h169 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem gemJoinX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 11 → (gemJoinSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [gemJoinLowArmEq I hsz 0 (by omega)]
      have hfalse : (gemJoinLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinLowSelBytes, gemJoinSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinLowArmEq I hsz 1 (by omega)]
      have hfalse : (gemJoinLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinLowSelBytes, gemJoinSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinLowArmEq I hsz 2 (by omega)]
      have hfalse : (gemJoinLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinLowSelBytes, gemJoinSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinLowArmEq I hsz 3 (by omega)]
      have hfalse : (gemJoinLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinLowSelBytes, gemJoinSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinLowArmEq I hsz 4 (by omega)]
      have hfalse : (gemJoinLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinLowSelBytes, gemJoinSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
  have heqHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [gemJoinHighArmEq I hsz 0 (by omega)]
      have hfalse : (gemJoinHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinHighArmEq I hsz 1 (by omega)]
      have hfalse : (gemJoinHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinHighArmEq I hsz 2 (by omega)]
      have hfalse : (gemJoinHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinHighArmEq I hsz 3 (by omega)]
      have hfalse : (gemJoinHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinHighArmEq I hsz 4 (by omega)]
      have hfalse : (gemJoinHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [gemJoinHighArmEq I hsz 5 (by omega)]
      have hfalse : (gemJoinHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [gemJoinHighSelBytes, gemJoinSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
  by_cases hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) ≠ ⟨0⟩
  · obtain ⟨_, _, hfirst⟩ :=
      gemJoinReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
    exact gemJoinLowNoMatchRevert hfirst heqLow
  · have hroot0 :
        UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    obtain ⟨_, _, hfirst⟩ :=
      gemJoinReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0
    exact gemJoinHighNoMatchRevert hfirst heqHigh

theorem gemJoinNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (gemJoinX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (gemJoinBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem gemJoinNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 11 → (gemJoinSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (gemJoinX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (gemJoinDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (gemJoinX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (gemJoinDispatch_none_short hshort)

end Benchmarks.Dss.GemJoin
