import Benchmarks.Dss.Spot.Trusted

/-!
# MakerDAO/Sky DSS Spotter dispatcher facts

Solm dispatch routing facts and the shared non-payable/no-selector runtime paths.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

attribute [local simp]
  cageSelectorBytes
  denySelectorBytes
  fileMatSelectorBytes
  fileParSelectorBytes
  filePipSelectorBytes
  ilksSelectorBytes
  liveSelectorBytes
  parSelectorBytes
  pokeSelectorBytes
  relySelectorBytes
  vatSelectorBytes
  wardsSelectorBytes

theorem spotDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 0)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 1)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchFileMat {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 2)) :
    dispatchMsg contract I.calldata = some fileMatTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileMatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchFilePar {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 3)) :
    dispatchMsg contract I.calldata = some fileParTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileParTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchFilePip {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 4)) :
    dispatchMsg contract I.calldata = some filePipTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some filePipTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchIlks {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 5)) :
    dispatchMsg contract I.calldata = some ilksTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ilksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 6)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchPar {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 7)) :
    dispatchMsg contract I.calldata = some parTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some parTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchPoke {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 8)) :
    dispatchMsg contract I.calldata = some pokeTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some pokeTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 9)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 10)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (spotSelBytes 11)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = spotSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem spotDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [cageTransition, denyTransition, fileMatTransition, fileParTransition, filePipTransition,
      ilksTransition, liveTransition, parTransition, pokeTransition, relyTransition,
      vatTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, cageSelectorBytes, denySelectorBytes, fileMatSelectorBytes,
        fileParSelectorBytes, filePipSelectorBytes, ilksSelectorBytes, liveSelectorBytes,
        parSelectorBytes, pokeSelectorBytes, relySelectorBytes, vatSelectorBytes,
        wardsSelectorBytes]
      native_decide) h

theorem spotDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 12 → (spotSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, cageSelectorBytes]
    simpa [spotSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [spotSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, fileMatSelectorBytes]
    simpa [spotSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, fileParSelectorBytes]
    simpa [spotSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, filePipSelectorBytes]
    simpa [spotSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, ilksSelectorBytes]
    simpa [spotSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [spotSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, parSelectorBytes]
    simpa [spotSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, pokeSelectorBytes]
    simpa [spotSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [spotSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [spotSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [spotSelBytes] using hnm 11 (by omega)

theorem spotBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Runtime dispatcher reachability -/

abbrev spotRootSplitPc : UInt256 := ⟨32⟩
abbrev spotHighFirstArmPc : UInt256 := ⟨43⟩
abbrev spotLowJumpdestPc : UInt256 := ⟨113⟩
abbrev spotLowFirstArmPc : UInt256 := ⟨114⟩
abbrev spotDispatchBodyPc : UInt256 := ⟨18⟩
abbrev spotSelectorLoadPc : UInt256 := ⟨26⟩
abbrev spotDispatchRevertPc : UInt256 := ⟨180⟩

def spotLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x15, 0x04, 0x46, 0x0f]⟩ -- poke(bytes32)
  | 1 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 2 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 3 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 4 => ⟨#[0x49, 0x5d, 0x32, 0xcb]⟩ -- par()
  | _ => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)

def spotHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 1 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 4 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)
  | _ => ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ -- file(bytes32,bytes32,address)

theorem spotSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    spotSelWord I = sel := by
  simpa [spotSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem spotRootSplitWellFormed :
    selectorSplitWellFormed spotBytecode spotRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem spotLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed spotBytecode
      (nthArmPc spotBytecode spotLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem spotHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed spotBytecode
      (nthArmPc spotBytecode spotHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem spotLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) =
      if (spotLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem spotHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) =
      if (spotHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem spotReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        spotRootSplitPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [spotRootSplitPc, spotSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := spotBytecode)
      (bodyPc := spotDispatchBodyPc) (loadPc := spotSelectorLoadPc)
      (firstPc := spotRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := spotDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem spotReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        spotLowFirstArmPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    spotReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h113 : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
      spotLowJumpdestPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [spotRootSplitPc, spotLowJumpdestPc] using
      RD.selectorSplitTakenAuto h32 spotRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h114 : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
      spotLowFirstArmPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [spotLowFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem spotReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        spotHighFirstArmPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    spotReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
      spotHighFirstArmPc [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [spotHighFirstArmPc, spotRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 spotRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem spotReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc i))
        (spotSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J spotBytecode 0).contains bodyPC = true)
    (hbody : armTgt spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    spotReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => spotLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem spotReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc i))
        (spotSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J spotBytecode 0).contains bodyPC = true)
    (hbody : armTgt spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    spotReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => spotHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem spotJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode spotBytecode pc = some (.Push .PUSH2, some (spotDispatchRevertPc, 2)))
    (hjump : decode spotBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h180 := h.push2 spotDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem spotLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) spotLowFirstArmPc
      [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h180 := h
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem spotHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) spotHighFirstArmPc
      [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (spotHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact spotJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem spotX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem spotX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt spotBytecode)
    (opC := solcGuardTgtOp spotBytecode)
    (wC := solcGuardTgtWidth spotBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h180 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 spotDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem spotX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 12 → (spotSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [spotLowArmEq I hsz 0 (by omega)]
      have hfalse : (spotLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [spotLowArmEq I hsz 1 (by omega)]
      have hfalse : (spotLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [spotLowArmEq I hsz 2 (by omega)]
      have hfalse : (spotLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [spotLowArmEq I hsz 3 (by omega)]
      have hfalse : (spotLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [spotLowArmEq I hsz 4 (by omega)]
      have hfalse : (spotLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [spotLowArmEq I hsz 5 (by omega)]
      have hfalse : (spotLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [spotLowSelBytes, spotSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
  have heqHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [spotHighArmEq I hsz 0 (by omega)]
      have hfalse : (spotHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [spotHighArmEq I hsz 1 (by omega)]
      have hfalse : (spotHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [spotHighArmEq I hsz 2 (by omega)]
      have hfalse : (spotHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [spotHighArmEq I hsz 3 (by omega)]
      have hfalse : (spotHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [spotHighArmEq I hsz 4 (by omega)]
      have hfalse : (spotHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [spotHighArmEq I hsz 5 (by omega)]
      have hfalse : (spotHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [spotHighSelBytes, spotSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩
  · obtain ⟨_, _, hfirst⟩ :=
      spotReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
    exact spotLowNoMatchRevert hfirst heqLow
  · have hroot0 : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    obtain ⟨_, _, hfirst⟩ :=
      spotReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0
    exact spotHighNoMatchRevert hfirst heqHigh

theorem spotNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (spotX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (spotBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem spotNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 12 → (spotSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (spotX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (spotDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (spotX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (spotDispatch_none_short hshort)

theorem spotNoSelectorMatches {I : ExecutionEnv}
    (hcage : ¬ selIs I (spotSelBytes 0))
    (hdeny : ¬ selIs I (spotSelBytes 1))
    (hfileMat : ¬ selIs I (spotSelBytes 2))
    (hfilePar : ¬ selIs I (spotSelBytes 3))
    (hfilePip : ¬ selIs I (spotSelBytes 4))
    (hilks : ¬ selIs I (spotSelBytes 5))
    (hlive : ¬ selIs I (spotSelBytes 6))
    (hpar : ¬ selIs I (spotSelBytes 7))
    (hpoke : ¬ selIs I (spotSelBytes 8))
    (hrely : ¬ selIs I (spotSelBytes 9))
    (hvat : ¬ selIs I (spotSelBytes 10))
    (hwards : ¬ selIs I (spotSelBytes 11)) :
    ∀ i, i < 12 → (spotSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, spotSelBytes] using hcage
  · simpa [selIs, spotSelBytes] using hdeny
  · simpa [selIs, spotSelBytes] using hfileMat
  · simpa [selIs, spotSelBytes] using hfilePar
  · simpa [selIs, spotSelBytes] using hfilePip
  · simpa [selIs, spotSelBytes] using hilks
  · simpa [selIs, spotSelBytes] using hlive
  · simpa [selIs, spotSelBytes] using hpar
  · simpa [selIs, spotSelBytes] using hpoke
  · simpa [selIs, spotSelBytes] using hrely
  · simpa [selIs, spotSelBytes] using hvat
  · simpa [selIs, spotSelBytes] using hwards

end Benchmarks.Dss.Spot
