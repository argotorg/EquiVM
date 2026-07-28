import Benchmarks.Dss.Pot.Trusted

/-!
# MakerDAO/Sky DSS Pot dispatcher facts

Solm dispatch routing facts, the shared non-payable body result, and the runtime dispatcher
reachability for the optimized depth-2 binary-search dispatcher.

Dispatch tree (pivots read off the bytecode):
* root split @32 (pivot `0x65fae35e`): `sel < pivot` → jump 162 → `163` ; else fall → `43`
* split @163 (pivot `0x2c69ed58`): `sel < pivot` → jump 222 → `223` ; else fall → `174`
* split @43  (pivot `0x9c52a7f1`): `sel < pivot` → jump 113 → `114` ; else fall → `54`

Linear-scan groups (arm order = bytecode order):
* `223`: join, pie, rho, file(bytes32,uint256)      (`sel < 0x2c69ed58`)
* `174`: Pie, vat, dsr, vow                          (`0x2c69ed58 ≤ sel < 0x65fae35e`)
* `114`: rely, cage, exit, live                      (`0x65fae35e ≤ sel < 0x9c52a7f1`)
* `54` : deny, drip, wards, chi, file(bytes32,address) (`sel ≥ 0x9c52a7f1`)
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

attribute [local simp]
  PieSelectorBytes cageSelectorBytes chiSelectorBytes denySelectorBytes dripSelectorBytes
  dsrSelectorBytes exitSelectorBytes fileDsrSelectorBytes fileVowSelectorBytes joinSelectorBytes
  liveSelectorBytes pieSelectorBytes relySelectorBytes rhoSelectorBytes vatSelectorBytes
  vowSelectorBytes wardsSelectorBytes

/-! ## Solm dispatch routing facts (selector → transition) -/

theorem potDispatchPie {I : ExecutionEnv} (hsel : selIs I (potSelBytes 0)) :
    dispatchMsg contract I.calldata = some PieTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some PieTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchCage {I : ExecutionEnv} (hsel : selIs I (potSelBytes 1)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchChi {I : ExecutionEnv} (hsel : selIs I (potSelBytes 2)) :
    dispatchMsg contract I.calldata = some chiTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some chiTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchDeny {I : ExecutionEnv} (hsel : selIs I (potSelBytes 3)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchDrip {I : ExecutionEnv} (hsel : selIs I (potSelBytes 4)) :
    dispatchMsg contract I.calldata = some dripTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dripTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchDsr {I : ExecutionEnv} (hsel : selIs I (potSelBytes 5)) :
    dispatchMsg contract I.calldata = some dsrTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dsrTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchExit {I : ExecutionEnv} (hsel : selIs I (potSelBytes 6)) :
    dispatchMsg contract I.calldata = some exitTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some exitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchFileDsr {I : ExecutionEnv} (hsel : selIs I (potSelBytes 7)) :
    dispatchMsg contract I.calldata = some fileDsrTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileDsrTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchFileVow {I : ExecutionEnv} (hsel : selIs I (potSelBytes 8)) :
    dispatchMsg contract I.calldata = some fileVowTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileVowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchJoin {I : ExecutionEnv} (hsel : selIs I (potSelBytes 9)) :
    dispatchMsg contract I.calldata = some joinTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some joinTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchLive {I : ExecutionEnv} (hsel : selIs I (potSelBytes 10)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchPieMap {I : ExecutionEnv} (hsel : selIs I (potSelBytes 11)) :
    dispatchMsg contract I.calldata = some pieTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some pieTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchRely {I : ExecutionEnv} (hsel : selIs I (potSelBytes 12)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchRho {I : ExecutionEnv} (hsel : selIs I (potSelBytes 13)) :
    dispatchMsg contract I.calldata = some rhoTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some rhoTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchVat {I : ExecutionEnv} (hsel : selIs I (potSelBytes 14)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchVow {I : ExecutionEnv} (hsel : selIs I (potSelBytes 15)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatchWards {I : ExecutionEnv} (hsel : selIs I (potSelBytes 16)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = potSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem potDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [PieTransition, cageTransition, chiTransition, denyTransition, dripTransition, dsrTransition,
      exitTransition, fileDsrTransition, fileVowTransition, joinTransition, liveTransition,
      pieTransition, relyTransition, rhoTransition, vatTransition, vowTransition,
      wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, PieSelectorBytes, cageSelectorBytes, chiSelectorBytes, denySelectorBytes,
        dripSelectorBytes, dsrSelectorBytes, exitSelectorBytes, fileDsrSelectorBytes,
        fileVowSelectorBytes, joinSelectorBytes, liveSelectorBytes, pieSelectorBytes,
        relySelectorBytes, rhoSelectorBytes, vatSelectorBytes, vowSelectorBytes,
        wardsSelectorBytes]
      native_decide) h

theorem potDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 17 → (potSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · rw [selectorOf, PieSelectorBytes]; simpa [potSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, cageSelectorBytes]; simpa [potSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, chiSelectorBytes]; simpa [potSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, denySelectorBytes]; simpa [potSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, dripSelectorBytes]; simpa [potSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, dsrSelectorBytes]; simpa [potSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, exitSelectorBytes]; simpa [potSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileDsrSelectorBytes]; simpa [potSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, fileVowSelectorBytes]; simpa [potSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, joinSelectorBytes]; simpa [potSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, liveSelectorBytes]; simpa [potSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, pieSelectorBytes]; simpa [potSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, relySelectorBytes]; simpa [potSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, rhoSelectorBytes]; simpa [potSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, vatSelectorBytes]; simpa [potSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, vowSelectorBytes]; simpa [potSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, wardsSelectorBytes]; simpa [potSelBytes] using hnm 16 (by omega)

theorem potBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Runtime dispatcher reachability -/

abbrev potDispatchBodyPc : UInt256 := ⟨18⟩
abbrev potSelectorLoadPc : UInt256 := ⟨26⟩
abbrev potRootSplitPc : UInt256 := ⟨32⟩
abbrev potSplit43Pc : UInt256 := ⟨43⟩
abbrev potJumpdest162Pc : UInt256 := ⟨162⟩
abbrev potSplit163Pc : UInt256 := ⟨163⟩
abbrev potG223JumpdestPc : UInt256 := ⟨222⟩
abbrev potG223FirstArmPc : UInt256 := ⟨223⟩
abbrev potG174FirstArmPc : UInt256 := ⟨174⟩
abbrev potG114JumpdestPc : UInt256 := ⟨113⟩
abbrev potG114FirstArmPc : UInt256 := ⟨114⟩
abbrev potG54FirstArmPc : UInt256 := ⟨54⟩
abbrev potDispatchRevertPc : UInt256 := ⟨267⟩

theorem potSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    potSelWord I = sel := by
  simpa [potSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem potRootSplitWellFormed : selectorSplitWellFormed potBytecode potRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem potSplit43WellFormed : selectorSplitWellFormed potBytecode potSplit43Pc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem potSplit163WellFormed : selectorSplitWellFormed potBytecode potSplit163Pc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem potG223ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed potBytecode (nthArmPc potBytecode potG223FirstArmPc j) := by
  intro j hj
  interval_cases j <;> (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem potG174ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed potBytecode (nthArmPc potBytecode potG174FirstArmPc j) := by
  intro j hj
  interval_cases j <;> (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem potG114ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed potBytecode (nthArmPc potBytecode potG114FirstArmPc j) := by
  intro j hj
  interval_cases j <;> (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem potG54ArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed potBytecode (nthArmPc potBytecode potG54FirstArmPc j) := by
  intro j hj
  interval_cases j <;> (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

/-- Reach the root split `@32` from the prologue. -/
theorem potReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potRootSplitPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [potRootSplitPc, potSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := potBytecode)
      (bodyPc := potDispatchBodyPc) (loadPc := potSelectorLoadPc)
      (firstPc := potRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := potDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Root split not taken (`sel ≥ 0x65fae35e`): fall through to split `@43`. -/
theorem potReach43 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potSplit43Pc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, h32⟩ :=
    potReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potSplit43Pc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k0 + 5) (C0 + 22) := by
    simpa [potSplit43Pc, potRootSplitPc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 potRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

/-- Root split taken (`sel < 0x65fae35e`): jump 162, step jumpdest to split `@163`. -/
theorem potReach163 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potSplit163Pc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, h32⟩ :=
    potReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h162 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potJumpdest162Pc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k0 + 5) (C0 + 22) := by
    simpa [potRootSplitPc, potJumpdest162Pc] using
      RD.selectorSplitTakenAuto h32 potRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h163 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potSplit163Pc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k0 + 5 + 1) (C0 + 22 + 1) := by
    simpa [potSplit163Pc, potJumpdest162Pc] using h162.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h163⟩

/-- Split `@43` taken (`sel < 0x9c52a7f1`): jump 113, step jumpdest to arms `@114`. -/
theorem potReachG114First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩)
    (h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potG114FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k1, C1, h43r⟩ :=
    potReach43 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h113 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG114JumpdestPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k1 + 5) (C1 + 22) := by
    simpa [potSplit43Pc, potG114JumpdestPc] using
      RD.selectorSplitTakenAuto h43r potSplit43WellFormed h43 (by jump_dest) (by simp)
  have h114 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG114FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k1 + 5 + 1) (C1 + 22 + 1) := by
    simpa [potG114FirstArmPc, potG114JumpdestPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

/-- Split `@43` not taken (`sel ≥ 0x9c52a7f1`): fall through to arms `@54`. -/
theorem potReachG54First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩)
    (h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potG54FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k1, C1, h43r⟩ :=
    potReach43 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG54FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k1 + 5) (C1 + 22) := by
    simpa [potG54FirstArmPc, potSplit43Pc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43r potSplit43WellFormed h43 (by simp)
  exact ⟨_, _, h54⟩

/-- Split `@163` taken (`sel < 0x2c69ed58`): jump 222, step jumpdest to arms `@223`. -/
theorem potReachG223First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩)
    (h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potG223FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k2, C2, h163r⟩ :=
    potReach163 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h222 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG223JumpdestPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k2 + 5) (C2 + 22) := by
    simpa [potSplit163Pc, potG223JumpdestPc] using
      RD.selectorSplitTakenAuto h163r potSplit163WellFormed h163 (by jump_dest) (by simp)
  have h223 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG223FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k2 + 5 + 1) (C2 + 22 + 1) := by
    simpa [potG223FirstArmPc, potG223JumpdestPc] using h222.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h223⟩

/-- Split `@163` not taken (`sel ≥ 0x2c69ed58`): fall through to arms `@174`. -/
theorem potReachG174First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩)
    (h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        potG174FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k2, C2, h163r⟩ :=
    potReach163 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h174 : RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
      potG174FirstArmPc [potSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k2 + 5) (C2 + 22) := by
    simpa [potG174FirstArmPc, potSplit163Pc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163r potSplit163WellFormed h163 (by simp)
  exact ⟨_, _, h174⟩

/-! ## Per-group linear-scan body reach (dispatcher fold) -/

theorem potReachG223Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩)
    (h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc i))
        (potSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J potBytecode 0).contains bodyPC = true)
    (hbody : armTgt potBytecode (nthArmPc potBytecode potG223FirstArmPc i) = bodyPC) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    potReachG223First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h163
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => potG223ArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem potReachG174Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩)
    (h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc i))
        (potSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J potBytecode 0).contains bodyPC = true)
    (hbody : armTgt potBytecode (nthArmPc potBytecode potG174FirstArmPc i) = bodyPC) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    potReachG174First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h163
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => potG174ArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem potReachG114Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩)
    (h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
        (potSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc i))
        (potSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J potBytecode 0).contains bodyPC = true)
    (hbody : armTgt potBytecode (nthArmPc potBytecode potG114FirstArmPc i) = bodyPC) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    potReachG114First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h43
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => potG114ArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem potReachG54Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩)
    (h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
        (potSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc i))
        (potSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J potBytecode 0).contains bodyPC = true)
    (hbody : armTgt potBytecode (nthArmPc potBytecode potG54FirstArmPc i) = bodyPC) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    potReachG54First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h43
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => potG54ArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

/-! ## Per-group arm selector bytes (arm order) + decode facts (for no-match revert) -/

def potG223SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x04, 0x98, 0x78, 0xf3]⟩ -- join
  | 1 => ⟨#[0x0b, 0xeb, 0xac, 0x86]⟩ -- pie
  | 2 => ⟨#[0x20, 0xab, 0xa0, 0x8b]⟩ -- rho
  | _ => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)

def potG174SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x2c, 0x69, 0xed, 0x58]⟩ -- Pie
  | 1 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat
  | 2 => ⟨#[0x48, 0x7b, 0xf0, 0x82]⟩ -- dsr
  | _ => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow

def potG114SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely
  | 1 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage
  | 2 => ⟨#[0x7f, 0x86, 0x61, 0xa1]⟩ -- exit
  | _ => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live

def potG54SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny
  | 1 => ⟨#[0x9f, 0x67, 0x8c, 0xca]⟩ -- drip
  | 2 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards
  | 3 => ⟨#[0xc9, 0x2a, 0xec, 0xc4]⟩ -- chi
  | _ => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)

theorem potG223ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j)) (potSelWord I) =
      if (potG223SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem potG174ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j)) (potSelWord I) =
      if (potG174SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem potG114ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j)) (potSelWord I) =
      if (potG114SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem potG54ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 5) :
    UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j)) (potSelWord I) =
      if (potG54SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

/-! ## Revert paths -/

/-- From a group-end cursor at `PUSH2 267; JUMP`, reach the shared no-match revert. -/
theorem potJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256} {k C : ℕ}
    (h : RD potBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode potBytecode pc = some (.Push .PUSH2, some (potDispatchRevertPc, 2)))
    (hjump : decode potBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h267 := h.push2 potDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h267 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem potG223NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD potBytecode I g (initState cA gh bl σ σ₀ g A I) potG223FirstArmPc
      [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h267 := h
    |>.selectorArmNotTakenAuto (potG223ArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG223ArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG223ArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG223ArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h267 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem potG174NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD potBytecode I g (initState cA gh bl σ σ₀ g A I) potG174FirstArmPc
      [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (potG174ArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG174ArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG174ArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG174ArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact potJumpToNoMatchRevert hend (by native_decide) (by native_decide)

theorem potG114NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD potBytecode I g (initState cA gh bl σ σ₀ g A I) potG114FirstArmPc
      [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
        (potSelWord I) = ⟨0⟩) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (potG114ArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG114ArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG114ArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG114ArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact potJumpToNoMatchRevert hend (by native_decide) (by native_decide)

theorem potG54NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD potBytecode I g (initState cA gh bl σ σ₀ g A I) potG54FirstArmPc
      [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
        (potSelWord I) = ⟨0⟩) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (potG54ArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG54ArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG54ArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG54ArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (potG54ArmsWellFormed 4 (by omega)) (heq0 4 (by omega)) (by simp)
  exact potJumpToNoMatchRevert hend (by native_decide) (by native_decide)

/-- `callvalue ≠ 0`: the non-payable prologue guard reverts. -/
theorem potX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- `calldatasize < 4`: the selector guard reverts. -/
theorem potX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt potBytecode)
    (opC := solcGuardTgtOp potBytecode)
    (wC := solcGuardTgtWidth potBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h267 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 potDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h267 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- No selector matches: the dispatcher routes to some group, scans all arms, and reverts. -/
theorem potX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 17 → (potSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩
  · -- low half (sel < 0x65fae35e): split @163
    by_cases h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩
    · -- group @223: join, pie, rho, file_bu
      have heq : ∀ j, j < 4 →
          UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
            (potSelWord I) = ⟨0⟩ := by
        intro j hj
        interval_cases j
        · rw [potG223ArmEq I hsz 0 (by omega),
            show (potG223SelBytes 0 == I.calldata.extract 0 4) = false from by
              simpa [potG223SelBytes, potSelBytes] using hnm 9 (by omega)]; rfl
        · rw [potG223ArmEq I hsz 1 (by omega),
            show (potG223SelBytes 1 == I.calldata.extract 0 4) = false from by
              simpa [potG223SelBytes, potSelBytes] using hnm 11 (by omega)]; rfl
        · rw [potG223ArmEq I hsz 2 (by omega),
            show (potG223SelBytes 2 == I.calldata.extract 0 4) = false from by
              simpa [potG223SelBytes, potSelBytes] using hnm 13 (by omega)]; rfl
        · rw [potG223ArmEq I hsz 3 (by omega),
            show (potG223SelBytes 3 == I.calldata.extract 0 4) = false from by
              simpa [potG223SelBytes, potSelBytes] using hnm 7 (by omega)]; rfl
      obtain ⟨_, _, hfirst⟩ :=
        potReachG223First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h163
      exact potG223NoMatchRevert hfirst heq
    · -- group @174: Pie, vat, dsr, vow
      have h163' : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩ := by
        by_contra hne; exact h163 hne
      have heq : ∀ j, j < 4 →
          UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
            (potSelWord I) = ⟨0⟩ := by
        intro j hj
        interval_cases j
        · rw [potG174ArmEq I hsz 0 (by omega),
            show (potG174SelBytes 0 == I.calldata.extract 0 4) = false from by
              simpa [potG174SelBytes, potSelBytes] using hnm 0 (by omega)]; rfl
        · rw [potG174ArmEq I hsz 1 (by omega),
            show (potG174SelBytes 1 == I.calldata.extract 0 4) = false from by
              simpa [potG174SelBytes, potSelBytes] using hnm 14 (by omega)]; rfl
        · rw [potG174ArmEq I hsz 2 (by omega),
            show (potG174SelBytes 2 == I.calldata.extract 0 4) = false from by
              simpa [potG174SelBytes, potSelBytes] using hnm 5 (by omega)]; rfl
        · rw [potG174ArmEq I hsz 3 (by omega),
            show (potG174SelBytes 3 == I.calldata.extract 0 4) = false from by
              simpa [potG174SelBytes, potSelBytes] using hnm 15 (by omega)]; rfl
      obtain ⟨_, _, hfirst⟩ :=
        potReachG174First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot h163'
      exact potG174NoMatchRevert hfirst heq
  · -- high half (sel ≥ 0x65fae35e): split @43
    have hroot' : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
      by_contra hne; exact hroot hne
    by_cases h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩
    · -- group @114: rely, cage, exit, live
      have heq : ∀ j, j < 4 →
          UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
            (potSelWord I) = ⟨0⟩ := by
        intro j hj
        interval_cases j
        · rw [potG114ArmEq I hsz 0 (by omega),
            show (potG114SelBytes 0 == I.calldata.extract 0 4) = false from by
              simpa [potG114SelBytes, potSelBytes] using hnm 12 (by omega)]; rfl
        · rw [potG114ArmEq I hsz 1 (by omega),
            show (potG114SelBytes 1 == I.calldata.extract 0 4) = false from by
              simpa [potG114SelBytes, potSelBytes] using hnm 1 (by omega)]; rfl
        · rw [potG114ArmEq I hsz 2 (by omega),
            show (potG114SelBytes 2 == I.calldata.extract 0 4) = false from by
              simpa [potG114SelBytes, potSelBytes] using hnm 6 (by omega)]; rfl
        · rw [potG114ArmEq I hsz 3 (by omega),
            show (potG114SelBytes 3 == I.calldata.extract 0 4) = false from by
              simpa [potG114SelBytes, potSelBytes] using hnm 10 (by omega)]; rfl
      obtain ⟨_, _, hfirst⟩ :=
        potReachG114First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot' h43
      exact potG114NoMatchRevert hfirst heq
    · -- group @54: deny, drip, wards, chi, file_ba
      have h43' : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩ := by
        by_contra hne; exact h43 hne
      have heq : ∀ j, j < 5 →
          UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
            (potSelWord I) = ⟨0⟩ := by
        intro j hj
        interval_cases j
        · rw [potG54ArmEq I hsz 0 (by omega),
            show (potG54SelBytes 0 == I.calldata.extract 0 4) = false from by
              simpa [potG54SelBytes, potSelBytes] using hnm 3 (by omega)]; rfl
        · rw [potG54ArmEq I hsz 1 (by omega),
            show (potG54SelBytes 1 == I.calldata.extract 0 4) = false from by
              simpa [potG54SelBytes, potSelBytes] using hnm 4 (by omega)]; rfl
        · rw [potG54ArmEq I hsz 2 (by omega),
            show (potG54SelBytes 2 == I.calldata.extract 0 4) = false from by
              simpa [potG54SelBytes, potSelBytes] using hnm 16 (by omega)]; rfl
        · rw [potG54ArmEq I hsz 3 (by omega),
            show (potG54SelBytes 3 == I.calldata.extract 0 4) = false from by
              simpa [potG54SelBytes, potSelBytes] using hnm 2 (by omega)]; rfl
        · rw [potG54ArmEq I hsz 4 (by omega),
            show (potG54SelBytes 4 == I.calldata.extract 0 4) = false from by
              simpa [potG54SelBytes, potSelBytes] using hnm 8 (by omega)]; rfl
      obtain ⟨_, _, hfirst⟩ :=
        potReachG54First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot' h43'
      exact potG54NoMatchRevert hfirst heq

end Benchmarks.Dss.Pot
