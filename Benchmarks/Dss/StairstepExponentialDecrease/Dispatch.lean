import Benchmarks.Dss.StairstepExponentialDecrease.Trusted

/-!
# MakerDAO/Sky DSS StairstepExponentialDecrease dispatcher facts

Solm dispatch routing facts and shared dispatcher-level proof obligations.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.StairstepExponentialDecrease

attribute [local simp]
  cutSelectorBytes
  denySelectorBytes
  fileSelectorBytes
  priceSelectorBytes
  relySelectorBytes
  stepSelectorBytes
  wardsSelectorBytes

theorem stairstepDispatchCut {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 0)) :
    dispatchMsg contract I.calldata = some cutTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cutTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 1)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchFile {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 2)) :
    dispatchMsg contract I.calldata = some fileTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchPrice {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 3)) :
    dispatchMsg contract I.calldata = some priceTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some priceTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 4)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchStep {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 5)) :
    dispatchMsg contract I.calldata = some stepTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some stepTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 6)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem stairstepDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [cutTransition, denyTransition, fileTransition, priceTransition, relyTransition,
      stepTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, cutSelectorBytes, denySelectorBytes, fileSelectorBytes,
        priceSelectorBytes, relySelectorBytes, stepSelectorBytes, wardsSelectorBytes]
      decide +native) h

theorem stairstepDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 7 → (stairstepSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, cutSelectorBytes]
    simpa [stairstepSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [stairstepSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, fileSelectorBytes]
    simpa [stairstepSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, priceSelectorBytes]
    simpa [stairstepSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [stairstepSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, stepSelectorBytes]
    simpa [stairstepSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [stairstepSelBytes] using hnm 6 (by omega)

theorem stairstepNoSelectorMatches {I : ExecutionEnv}
    (hcut : ¬ selIs I (stairstepSelBytes 0))
    (hdeny : ¬ selIs I (stairstepSelBytes 1))
    (hfile : ¬ selIs I (stairstepSelBytes 2))
    (hprice : ¬ selIs I (stairstepSelBytes 3))
    (hrely : ¬ selIs I (stairstepSelBytes 4))
    (hstep : ¬ selIs I (stairstepSelBytes 5))
    (hwards : ¬ selIs I (stairstepSelBytes 6)) :
    ∀ i, i < 7 → (stairstepSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, stairstepSelBytes] using hcut
  · simpa [selIs, stairstepSelBytes] using hdeny
  · simpa [selIs, stairstepSelBytes] using hfile
  · simpa [selIs, stairstepSelBytes] using hprice
  · simpa [selIs, stairstepSelBytes] using hrely
  · simpa [selIs, stairstepSelBytes] using hstep
  · simpa [selIs, stairstepSelBytes] using hwards

/-! ## Runtime dispatcher PCs and selector arms

These constants are read from `runtime.hex`; keep them synchronized with
`stairstepExponentialDecreaseBytecode`.
-/

abbrev stairstepRootSplitPc : UInt256 := ⟨32⟩
abbrev stairstepHighFirstArmPc : UInt256 := ⟨43⟩
abbrev stairstepLowJumpdestPc : UInt256 := ⟨91⟩
abbrev stairstepLowFirstArmPc : UInt256 := ⟨92⟩
abbrev stairstepDispatchBodyPc : UInt256 := ⟨18⟩
abbrev stairstepSelectorLoadPc : UInt256 := ⟨26⟩
abbrev stairstepDispatchRevertPc : UInt256 := ⟨125⟩

def stairstepLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 1 => ⟨#[0x48, 0x7a, 0x23, 0x95]⟩ -- price(uint256,uint256)
  | _ => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)

def stairstepHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 1 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 2 => ⟨#[0xe2, 0x5f, 0xe1, 0x75]⟩ -- step()
  | _ => ⟨#[0xe6, 0xfd, 0x60, 0x4c]⟩ -- cut()

abbrev stairstepFileEntryPc : UInt256 := ⟨130⟩
abbrev stairstepPriceEntryPc : UInt256 := ⟨167⟩
abbrev stairstepRelyEntryPc : UInt256 := ⟨220⟩
abbrev stairstepDenyEntryPc : UInt256 := ⟨258⟩
abbrev stairstepWardsEntryPc : UInt256 := ⟨296⟩
abbrev stairstepStepEntryPc : UInt256 := ⟨334⟩
abbrev stairstepCutEntryPc : UInt256 := ⟨342⟩

theorem stairstepBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem stairstepSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    stairstepSelWord I = sel := by
  simpa [stairstepSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem stairstepRootSplitWellFormed :
    selectorSplitWellFormed stairstepExponentialDecreaseBytecode stairstepRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

set_option maxHeartbeats 1000000 in
theorem stairstepLowArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed stairstepExponentialDecreaseBytecode
      (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem stairstepHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed stairstepExponentialDecreaseBytecode
      (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

theorem stairstepLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc j))
        (stairstepSelWord I) =
      if (stairstepLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem stairstepHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j))
        (stairstepSelWord I) =
      if (stairstepHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem stairstepReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepRootSplitPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [stairstepRootSplitPc, stairstepSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := stairstepExponentialDecreaseBytecode)
      (bodyPc := stairstepDispatchBodyPc) (loadPc := stairstepSelectorLoadPc)
      (firstPc := stairstepRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := stairstepDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)

theorem stairstepReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepLowFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    stairstepReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h91 : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepLowJumpdestPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [stairstepRootSplitPc, stairstepLowJumpdestPc] using
      RD.selectorSplitTakenAuto h32 stairstepRootSplitWellFormed hroot (by jump_dest)
        (by simp)
  have h92 : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepLowFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [stairstepLowFirstArmPc] using h91.jumpdest (by decide +native) (by simp)
  exact ⟨_, _, h92⟩

theorem stairstepReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) = ⟨0⟩) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepHighFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    stairstepReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepHighFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [stairstepHighFirstArmPc, stairstepRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 stairstepRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem stairstepReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc i))
        (stairstepSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J stairstepExponentialDecreaseBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt stairstepExponentialDecreaseBytecode
        (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    stairstepReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => stairstepLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem stairstepReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc i))
        (stairstepSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J stairstepExponentialDecreaseBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt stairstepExponentialDecreaseBytecode
        (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    stairstepReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => stairstepHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem stairstepJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush :
      decode stairstepExponentialDecreaseBytecode pc =
        some (.Push .PUSH2, some (stairstepDispatchRevertPc, 2)))
    (hjump :
      decode stairstepExponentialDecreaseBytecode (pc + UInt256.ofNat 3) =
        some (.JUMP, .none)) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h125 := h.push2 stairstepDispatchRevertPc hpush
    (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h125 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem stairstepLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepLowFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h125 := h
    |>.selectorArmNotTakenAuto (stairstepLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h125 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem stairstepHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepHighFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h87 := h
    |>.selectorArmNotTakenAuto (stairstepHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact stairstepJumpToNoMatchRevert h87 (by decide +native) (by decide +native)

theorem stairstepX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  have h12 := h0.push2 ⟨16⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiNT (by decide +native) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

theorem stairstepX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt stairstepExponentialDecreaseBytecode)
    (opC := solcGuardTgtOp stairstepExponentialDecreaseBytecode)
    (wC := solcGuardTgtWidth stairstepExponentialDecreaseBytecode) h0 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest)
  have h125 := h1.push1 ⟨4⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.calldatasize (by decide +native) (by simp only [List.length]; omega)
    |>.lt (by decide +native) (by simp only [List.length]; omega)
    |>.push2 stairstepDispatchRevertPc (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiT (by decide +native) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h125 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

theorem stairstepX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 7 → (stairstepSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev stairstepExponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepLowFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [stairstepLowArmEq I hsz 0 (by omega)]
      have hfalse : (stairstepLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [stairstepLowSelBytes, stairstepSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepLowArmEq I hsz 1 (by omega)]
      have hfalse : (stairstepLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [stairstepLowSelBytes, stairstepSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepLowArmEq I hsz 2 (by omega)]
      have hfalse : (stairstepLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [stairstepLowSelBytes, stairstepSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
  have heqHigh : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [stairstepHighArmEq I hsz 0 (by omega)]
      have hfalse : (stairstepHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [stairstepHighSelBytes, stairstepSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepHighArmEq I hsz 1 (by omega)]
      have hfalse : (stairstepHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [stairstepHighSelBytes, stairstepSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepHighArmEq I hsz 2 (by omega)]
      have hfalse : (stairstepHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [stairstepHighSelBytes, stairstepSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepHighArmEq I hsz 3 (by omega)]
      have hfalse : (stairstepHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [stairstepHighSelBytes, stairstepSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  by_cases hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) ≠ ⟨0⟩
  · obtain ⟨_, _, hfirst⟩ :=
      stairstepReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
    exact stairstepLowNoMatchRevert hfirst heqLow
  · have hroot0 :
        UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
          (stairstepSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    obtain ⟨_, _, hfirst⟩ :=
      stairstepReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0
    exact stairstepHighNoMatchRevert hfirst heqHigh

theorem stairstepNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (stairstepX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (stairstepBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem stairstepNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 7 → (stairstepSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (stairstepX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (stairstepDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (stairstepX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (stairstepDispatch_none_short hshort)

end Benchmarks.Dss.StairstepExponentialDecrease
