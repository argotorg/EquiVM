import Benchmarks.Dss.Jug.Trusted

/-!
# MakerDAO/Sky DSS Jug dispatcher facts

Solm dispatch routing facts and the shared non-payable body result.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

attribute [local simp]
  baseSelectorBytes
  denySelectorBytes
  dripSelectorBytes
  fileBaseSelectorBytes
  fileDutySelectorBytes
  fileVowSelectorBytes
  ilksSelectorBytes
  initSelectorBytes
  relySelectorBytes
  vatSelectorBytes
  vowSelectorBytes
  wardsSelectorBytes

theorem jugDispatchBase {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 0)) :
    dispatchMsg contract I.calldata = some baseTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some baseTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 1)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchDrip {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 2)) :
    dispatchMsg contract I.calldata = some dripTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dripTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchFileBase {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 3)) :
    dispatchMsg contract I.calldata = some fileBaseTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileBaseTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchFileDuty {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 4)) :
    dispatchMsg contract I.calldata = some fileDutyTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileDutyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchFileVow {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 5)) :
    dispatchMsg contract I.calldata = some fileVowTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileVowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchIlks {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 6)) :
    dispatchMsg contract I.calldata = some ilksTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ilksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchInit {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 7)) :
    dispatchMsg contract I.calldata = some initTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some initTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 8)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 9)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchVow {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 10)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (jugSelBytes 11)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = jugSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem jugDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [baseTransition, denyTransition, dripTransition, fileBaseTransition, fileDutyTransition,
      fileVowTransition, ilksTransition, initTransition, relyTransition, vatTransition,
      vowTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, baseSelectorBytes, denySelectorBytes, dripSelectorBytes,
        fileBaseSelectorBytes, fileDutySelectorBytes, fileVowSelectorBytes, ilksSelectorBytes,
        initSelectorBytes, relySelectorBytes, vatSelectorBytes, vowSelectorBytes,
        wardsSelectorBytes]
      decide +native) h

theorem jugDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 12 → (jugSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, baseSelectorBytes]
    simpa [jugSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [jugSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, dripSelectorBytes]
    simpa [jugSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, fileBaseSelectorBytes]
    simpa [jugSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, fileDutySelectorBytes]
    simpa [jugSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, fileVowSelectorBytes]
    simpa [jugSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, ilksSelectorBytes]
    simpa [jugSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, initSelectorBytes]
    simpa [jugSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [jugSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [jugSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [jugSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [jugSelBytes] using hnm 11 (by omega)

theorem jugBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Runtime dispatcher reachability -/

abbrev jugRootSplitPc : UInt256 := ⟨32⟩
abbrev jugHighFirstArmPc : UInt256 := ⟨43⟩
abbrev jugLowJumpdestPc : UInt256 := ⟨113⟩
abbrev jugLowFirstArmPc : UInt256 := ⟨114⟩
abbrev jugDispatchBodyPc : UInt256 := ⟨18⟩
abbrev jugSelectorLoadPc : UInt256 := ⟨26⟩
abbrev jugDispatchRevertPc : UInt256 := ⟨180⟩

def jugLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 3 => ⟨#[0x3b, 0x66, 0x31, 0x95]⟩ -- init(bytes32)
  | 4 => ⟨#[0x44, 0xe2, 0xa5, 0xa8]⟩ -- drip(bytes32)
  | _ => ⟨#[0x50, 0x01, 0xf3, 0xb5]⟩  -- base()

def jugHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | 1 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 4 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | _ => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩  -- ilks(bytes32)

theorem jugSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    jugSelWord I = sel := by
  simpa [jugSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem jugRootSplitWellFormed :
    selectorSplitWellFormed jugBytecode jugRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

set_option maxHeartbeats 1000000 in
theorem jugLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed jugBytecode
      (nthArmPc jugBytecode jugLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem jugHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed jugBytecode
      (nthArmPc jugBytecode jugHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

theorem jugLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) =
      if (jugLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem jugHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) =
      if (jugHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem jugReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        jugRootSplitPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [jugRootSplitPc, jugSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := jugBytecode)
      (bodyPc := jugDispatchBodyPc) (loadPc := jugSelectorLoadPc)
      (firstPc := jugRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := jugDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)

theorem jugReachLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        jugLowFirstArmPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    jugReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h113 : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
      jugLowJumpdestPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [jugRootSplitPc, jugLowJumpdestPc] using
      RD.selectorSplitTakenAuto h32 jugRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h114 : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
      jugLowFirstArmPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [jugLowFirstArmPc] using h113.jumpdest (by decide +native) (by simp)
  exact ⟨_, _, h114⟩

theorem jugReachHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        jugHighFirstArmPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    jugReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
      jugHighFirstArmPc [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [jugHighFirstArmPc, jugRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 jugRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem jugReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc i))
        (jugSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J jugBytecode 0).contains bodyPC = true)
    (hbody : armTgt jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    jugReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => jugLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem jugReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc i))
        (jugSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J jugBytecode 0).contains bodyPC = true)
    (hbody : armTgt jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    jugReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => jugHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem jugJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode jugBytecode pc = some (.Push .PUSH2, some (jugDispatchRevertPc, 2)))
    (hjump : decode jugBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h180 := h.push2 jugDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem jugLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) jugLowFirstArmPc
      [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h180 := h
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem jugHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) jugHighFirstArmPc
      [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (jugHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact jugJumpToNoMatchRevert h109 (by decide +native) (by decide +native)

theorem jugX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  have h12 := h0.push2 ⟨16⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiNT (by decide +native) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

theorem jugX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt jugBytecode)
    (opC := solcGuardTgtOp jugBytecode)
    (wC := solcGuardTgtWidth jugBytecode) h0 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest)
  have h180 := h1.push1 ⟨4⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.calldatasize (by decide +native) (by simp only [List.length]; omega)
    |>.lt (by decide +native) (by simp only [List.length]; omega)
    |>.push2 jugDispatchRevertPc (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiT (by decide +native) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h180 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

theorem jugX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 12 → (jugSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [jugLowArmEq I hsz 0 (by omega)]
      have hfalse : (jugLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [jugLowArmEq I hsz 1 (by omega)]
      have hfalse : (jugLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [jugLowArmEq I hsz 2 (by omega)]
      have hfalse : (jugLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [jugLowArmEq I hsz 3 (by omega)]
      have hfalse : (jugLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [jugLowArmEq I hsz 4 (by omega)]
      have hfalse : (jugLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [jugLowArmEq I hsz 5 (by omega)]
      have hfalse : (jugLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [jugLowSelBytes, jugSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  have heqHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [jugHighArmEq I hsz 0 (by omega)]
      have hfalse : (jugHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [jugHighArmEq I hsz 1 (by omega)]
      have hfalse : (jugHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [jugHighArmEq I hsz 2 (by omega)]
      have hfalse : (jugHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [jugHighArmEq I hsz 3 (by omega)]
      have hfalse : (jugHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [jugHighArmEq I hsz 4 (by omega)]
      have hfalse : (jugHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [jugHighArmEq I hsz 5 (by omega)]
      have hfalse : (jugHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [jugHighSelBytes, jugSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩
  · obtain ⟨_, _, hfirst⟩ :=
      jugReachLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
    exact jugLowNoMatchRevert hfirst heqLow
  · have hroot0 : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    obtain ⟨_, _, hfirst⟩ :=
      jugReachHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0
    exact jugHighNoMatchRevert hfirst heqHigh

end Benchmarks.Dss.Jug
