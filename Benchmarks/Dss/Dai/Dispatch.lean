import Benchmarks.Dss.Dai.Trusted

/-!
# MakerDAO DSS Dai dispatcher reach slices

The optimized Dai runtime uses a three-split selector tree.  These facts stop at function wrapper
entry points and are intended to feed the per-function body proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## Solm dispatch routing -/

attribute [local simp]
  daiAllowanceSelectorBytes
  daiApproveSelectorBytes
  daiBalanceOfSelectorBytes
  daiBurnSelectorBytes
  daiDecimalsSelectorBytes
  daiDenySelectorBytes
  daiDomainSeparatorSelectorBytes
  daiMintSelectorBytes
  daiMoveSelectorBytes
  daiNameSelectorBytes
  daiNoncesSelectorBytes
  daiPermitSelectorBytes
  daiPermitTypehashSelectorBytes
  daiPullSelectorBytes
  daiPushSelectorBytes
  daiRelySelectorBytes
  daiSymbolSelectorBytes
  daiTotalSupplySelectorBytes
  daiTransferSelectorBytes
  daiTransferFromSelectorBytes
  daiVersionSelectorBytes
  daiWardsSelectorBytes

theorem daiDispatchAllowance {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 0)) :
    dispatchMsg contract I.calldata = some allowanceTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 0 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some allowanceTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 21)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 21 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchBalanceOf {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 2)) :
    dispatchMsg contract I.calldata = some balanceOfTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 2 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some balanceOfTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchDecimals {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 4)) :
    dispatchMsg contract I.calldata = some decimalsTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 4 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some decimalsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchDomainSeparator {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 6)) :
    dispatchMsg contract I.calldata = some domainSeparatorTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 6 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some domainSeparatorTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchPermitTypehash {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 12)) :
    dispatchMsg contract I.calldata = some permitTypehashTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 12 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some permitTypehashTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchNonces {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 10)) :
    dispatchMsg contract I.calldata = some noncesTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 10 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some noncesTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchTotalSupply {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 17)) :
    dispatchMsg contract I.calldata = some totalSupplyTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 17 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some totalSupplyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchTransferFrom {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 19)) :
    dispatchMsg contract I.calldata = some transferFromTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 19 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some transferFromTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchName {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 9)) :
    dispatchMsg contract I.calldata = some nameTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 9 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some nameTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchSymbol {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 16)) :
    dispatchMsg contract I.calldata = some symbolTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 16 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some symbolTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchVersion {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 20)) :
    dispatchMsg contract I.calldata = some versionTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 20 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some versionTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchApprove {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 1)) :
    dispatchMsg contract I.calldata = some approveTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 1 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some approveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 5)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 5 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 15)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 15 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchBurn {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 3)) :
    dispatchMsg contract I.calldata = some burnTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 3 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some burnTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchMint {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 7)) :
    dispatchMsg contract I.calldata = some mintTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 7 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some mintTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchMove {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 8)) :
    dispatchMsg contract I.calldata = some moveTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 8 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some moveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchPermit {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 11)) :
    dispatchMsg contract I.calldata = some permitTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 11 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some permitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchPull {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 13)) :
    dispatchMsg contract I.calldata = some pullTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 13 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some pullTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchPush {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 14)) :
    dispatchMsg contract I.calldata = some pushTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 14 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some pushTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem daiDispatchTransfer {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 18)) :
    dispatchMsg contract I.calldata = some transferTransition := by
  have hcd : I.calldata.extract 0 4 = daiSelBytes 18 :=
    (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some transferTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

/-! ## Dispatcher layout -/

/-- Root `GT` split at selector pivot `0x7ecebe00`. -/
abbrev daiRootSplitPc : UInt256 := ⟨32⟩

/-- High-half `GT` split at selector pivot `0xa9059cbb`. -/
abbrev daiHighSplitPc : UInt256 := ⟨43⟩

/-- Low-half `GT` split at selector pivot `0x313ce567`. -/
abbrev daiLowSplitPc : UInt256 := ⟨185⟩

/-- First arm for selectors `>= 0xa9059cbb`. -/
abbrev daiVeryHighFirstArmPc : UInt256 := ⟨54⟩

/-- First arm for selectors `>= 0x7ecebe00` and `< 0xa9059cbb`. -/
abbrev daiHighFirstArmPc : UInt256 := ⟨125⟩

/-- First arm for selectors `>= 0x313ce567` and `< 0x7ecebe00`. -/
abbrev daiLowFirstArmPc : UInt256 := ⟨196⟩

/-- First arm for selectors `< 0x313ce567`. -/
abbrev daiVeryLowFirstArmPc : UInt256 := ⟨267⟩

set_option maxHeartbeats 1000000 in
/-- The very-high selector group contains six linear `EQ` arms. -/
theorem daiVeryHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed daiBytecode
      (nthArmPc daiBytecode daiVeryHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high selector group contains five linear `EQ` arms. -/
theorem daiHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed daiBytecode
      (nthArmPc daiBytecode daiHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The low selector group contains six linear `EQ` arms. -/
theorem daiLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed daiBytecode
      (nthArmPc daiBytecode daiLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The very-low selector group contains five linear `EQ` arms. -/
theorem daiVeryLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed daiBytecode
      (nthArmPc daiBytecode daiVeryLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

/-- The root selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem daiRootSplitWellFormed :
    selectorSplitWellFormed daiBytecode daiRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem daiHighSplitWellFormed :
    selectorSplitWellFormed daiBytecode daiHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The low selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem daiLowSplitWellFormed :
    selectorSplitWellFormed daiBytecode daiLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem daiSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    daiSelWord I = sel := by
  simpa [daiSelWord] using solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

/-! ## Shared prefix and high selector branch -/

/-- Standard solc prologue/guards/selector load, stopping at Dai's root selector split. -/
theorem daiReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiRootSplitPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [daiRootSplitPc, daiSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := daiBytecode)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := daiRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := (⟨322⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)

/-- Reach the first arm in Dai's very-high selector group. -/
theorem daiReachVeryHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat daiBytecode daiHighSplitPc) (daiSelWord I) = ⟨0⟩) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiVeryHighFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiHighSplitPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiHighSplitPc, daiRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 daiRootSplitWellFormed hroot (by simp)
  have h54 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiVeryHighFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [daiVeryHighFirstArmPc, daiHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 daiHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

/-- Reach a body in Dai's very-high selector group. -/
theorem daiReachVeryHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat daiBytecode daiHighSplitPc) (daiSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryHighFirstArmPc j))
        (daiSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryHighFirstArmPc i))
        (daiSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiBytecode (nthArmPc daiBytecode daiVeryHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiReachVeryHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiVeryHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ## High selector branch -/

theorem daiReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat daiBytecode daiHighSplitPc) (daiSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiHighFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiHighSplitPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiHighSplitPc, daiRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 daiRootSplitWellFormed hroot (by simp)
  have h124 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨124⟩ [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [daiHighSplitPc] using
      RD.selectorSplitTakenAuto h43 daiHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h125 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiHighFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [daiHighFirstArmPc] using h124.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h125⟩

theorem daiReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat daiBytecode daiHighSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiBytecode (nthArmPc daiBytecode daiHighFirstArmPc j))
        (daiSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiHighFirstArmPc i))
        (daiSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiBytecode (nthArmPc daiBytecode daiHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ## Low selector branch -/

theorem daiReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat daiBytecode daiLowSplitPc) (daiSelWord I) = ⟨0⟩) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiLowFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h184 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨184⟩ [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiRootSplitPc] using
      RD.selectorSplitTakenAuto h32 daiRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h185 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiLowSplitPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [daiLowSplitPc] using h184.jumpdest (by native_decide) (by simp)
  have h196 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiLowFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [daiLowFirstArmPc, daiLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h185 daiLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h196⟩

theorem daiReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat daiBytecode daiLowSplitPc) (daiSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiBytecode (nthArmPc daiBytecode daiLowFirstArmPc j))
        (daiSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiLowFirstArmPc i))
        (daiSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiBytecode (nthArmPc daiBytecode daiLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ## Very-low selector branch -/

theorem daiReachVeryLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat daiBytecode daiLowSplitPc) (daiSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
        daiVeryLowFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    daiReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h184 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨184⟩ [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [daiRootSplitPc] using
      RD.selectorSplitTakenAuto h32 daiRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h185 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiLowSplitPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [daiLowSplitPc] using h184.jumpdest (by native_decide) (by simp)
  have h266 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨266⟩ [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [daiLowSplitPc] using
      RD.selectorSplitTakenAuto h185 daiLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h267 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I)
      daiVeryLowFirstArmPc [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [daiVeryLowFirstArmPc] using h266.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h267⟩

theorem daiReachVeryLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat daiBytecode daiLowSplitPc) (daiSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryLowFirstArmPc j))
        (daiSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryLowFirstArmPc i))
        (daiSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J daiBytecode 0).contains bodyPC = true)
    (hbody : armTgt daiBytecode (nthArmPc daiBytecode daiVeryLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    daiReachVeryLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => daiVeryLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

theorem daiReachBalanceOfBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 2)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨734⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x70a08231⟩ :=
    daiSelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 ⟨0x70a08231⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 5 (by decide) ⟨734⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `decimals()`'s external wrapper at pc `604`. -/
theorem daiReachDecimalsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 4)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨604⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x313ce567⟩ :=
    daiSelWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨0x313ce567⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 0 (by decide) ⟨604⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `DOMAIN_SEPARATOR()`'s external wrapper at pc `634`. -/
theorem daiReachDomainSeparatorBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 6)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨634⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x3644e515⟩ :=
    daiSelWord_eq_of_beq I hsz 0x36 0x44 0xe5 0x15 ⟨0x3644e515⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 1 (by decide) ⟨634⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `totalSupply()`'s external wrapper at pc `516`. -/
theorem daiReachTotalSupplyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 17)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨516⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x18160ddd⟩ :=
    daiSelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨0x18160ddd⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryLowBody 2 (by decide) ⟨516⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `transferFrom(address,address,uint256)`'s external wrapper at pc `542`. -/
theorem daiReachTransferFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 19)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨542⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x23b872dd⟩ :=
    daiSelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨0x23b872dd⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryLowBody 3 (by decide) ⟨542⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `PERMIT_TYPEHASH()`'s external wrapper at pc `596`. -/
theorem daiReachPermitTypehashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 12)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨596⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x30adf81f⟩ :=
    daiSelWord_eq_of_beq I hsz 0x30 0xad 0xf8 0x1f ⟨0x30adf81f⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryLowBody 4 (by decide) ⟨596⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `nonces(address)`'s external wrapper at pc `772`. -/
theorem daiReachNoncesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 10)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨772⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x7ecebe00⟩ :=
    daiSelWord_eq_of_beq I hsz 0x7e 0xce 0xbe 0x00 ⟨0x7ecebe00⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachHighBody 0 (by decide) ⟨772⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `allowance(address,address)`'s external wrapper at pc `1170`. -/
theorem daiReachAllowanceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 0)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1170⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xdd62ed3e⟩ :=
    daiSelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e ⟨0xdd62ed3e⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 4 (by decide) ⟨1170⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `wards(address)`'s external wrapper at pc `1132`. -/
theorem daiReachWardsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 21)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1132⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xbf353dbb⟩ :=
    daiSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 3 (by decide) ⟨1132⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `name()`'s external wrapper at pc `327`. -/
theorem daiReachNameBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 9)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨327⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x06fdde03⟩ :=
    daiSelWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨0x06fdde03⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryLowBody 0 (by decide) ⟨327⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `symbol()`'s external wrapper at pc `900`. -/
theorem daiReachSymbolBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 16)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨900⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x95d89b41⟩ :=
    daiSelWord_eq_of_beq I hsz 0x95 0xd8 0x9b 0x41 ⟨0x95d89b41⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachHighBody 2 (by decide) ⟨900⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `version()`'s external wrapper at pc `688`. -/
theorem daiReachVersionBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 20)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨688⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x54fd4d50⟩ :=
    daiSelWord_eq_of_beq I hsz 0x54 0xfd 0x4d 0x50 ⟨0x54fd4d50⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 3 (by decide) ⟨688⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `approve(address,uint256)`'s external wrapper at pc `452`. -/
theorem daiReachApproveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 1)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨452⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x095ea7b3⟩ :=
    daiSelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨0x095ea7b3⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryLowBody 1 (by decide) ⟨452⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `deny(address)`'s external wrapper at pc `908`. -/
theorem daiReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 5)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨908⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x9c52a7f1⟩ :=
    daiSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachHighBody 3 (by decide) ⟨908⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `rely(address)`'s external wrapper at pc `696`. -/
theorem daiReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 15)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨696⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x65fae35e⟩ :=
    daiSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 4 (by decide) ⟨696⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `burn(address,uint256)`'s external wrapper at pc `946`. -/
theorem daiReachBurnBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 3)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨946⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x9dc29fac⟩ :=
    daiSelWord_eq_of_beq I hsz 0x9d 0xc2 0x9f 0xac ⟨0x9dc29fac⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachHighBody 4 (by decide) ⟨946⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `mint(address,uint256)`'s external wrapper at pc `642`. -/
theorem daiReachMintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 7)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨642⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x40c10f19⟩ :=
    daiSelWord_eq_of_beq I hsz 0x40 0xc1 0x0f 0x19 ⟨0x40c10f19⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachLowBody 2 (by decide) ⟨642⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `move(address,address,uint256)`'s external wrapper at pc `1078`. -/
theorem daiReachMoveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 8)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1078⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xbb35783b⟩ :=
    daiSelWord_eq_of_beq I hsz 0xbb 0x35 0x78 0x3b ⟨0xbb35783b⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 2 (by decide) ⟨1078⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `permit(...)`'s external wrapper at pc `810`. -/
theorem daiReachPermitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 11)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨810⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0x8fcbaf0c⟩ :=
    daiSelWord_eq_of_beq I hsz 0x8f 0xcb 0xaf 0x0c ⟨0x8fcbaf0c⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachHighBody 1 (by decide) ⟨810⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `pull(address,uint256)`'s external wrapper at pc `1216`. -/
theorem daiReachPullBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 13)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xf2d5d56b⟩ :=
    daiSelWord_eq_of_beq I hsz 0xf2 0xd5 0xd5 0x6b ⟨0xf2d5d56b⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 5 (by decide) ⟨1216⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `push(address,uint256)`'s external wrapper at pc `1034`. -/
theorem daiReachPushBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 14)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1034⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xb753a98c⟩ :=
    daiSelWord_eq_of_beq I hsz 0xb7 0x53 0xa9 0x8c ⟨0xb753a98c⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 1 (by decide) ⟨1034⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> native_decide)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

/-- Reach `transfer(address,uint256)`'s external wrapper at pc `990`. -/
theorem daiReachTransferBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiSelBytes 18)) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨990⟩
        [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : daiSelWord I = ⟨0xa9059cbb⟩ :=
    daiSelWord_eq_of_beq I hsz 0xa9 0x05 0x9c 0xbb ⟨0xa9059cbb⟩
      (by native_decide) (by simpa [daiSelBytes] using hsel)
  exact daiReachVeryHighBody 0 (by decide) ⟨990⟩ hcode hwv hsz hsize
    (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
    (fun j hj => by omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)

end Benchmarks.Dss.Dai
