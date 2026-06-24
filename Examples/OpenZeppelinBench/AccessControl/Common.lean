import Examples.OpenZeppelinBench.AccessControl.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark shared proof foundation

Phase 0 facts for the one-level binary-search dispatcher plus scalar ABI return helpers.
-/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev accessControlSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def accessControlSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩  -- DEFAULT_ADMIN_ROLE
  | 1 => ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩  -- getRoleAdmin
  | 2 => ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩  -- grantRole
  | 3 => ⟨#[0x91, 0xd1, 0x48, 0x54]⟩  -- hasRole
  | 4 => ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩  -- renounceRole
  | 5 => ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩  -- revokeRole
  | _ => ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩  -- supportsInterface

/-- Low selector half in bytecode arm order. -/
def accessControlLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩  -- supportsInterface
  | 1 => ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩  -- getRoleAdmin
  | _ => ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩  -- grantRole

/-- High selector half in bytecode arm order. -/
def accessControlHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩  -- renounceRole
  | 1 => ⟨#[0x91, 0xd1, 0x48, 0x54]⟩  -- hasRole
  | 2 => ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩  -- DEFAULT_ADMIN_ROLE
  | _ => ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩  -- revokeRole

/-! ## Binary-search dispatcher constants -/

abbrev accessControlSplitPc : UInt256 := ⟨30⟩
abbrev accessControlHighFirstArmPc : UInt256 := ⟨41⟩
abbrev accessControlLowJumpdestPc : UInt256 := ⟨88⟩
abbrev accessControlLowFirstArmPc : UInt256 := ⟨89⟩

theorem accessControlSplitWellFormed :
    selectorSplitWellFormed accessControlBenchBytecode accessControlSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem accessControlHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed accessControlBenchBytecode
      (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem accessControlLowArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed accessControlBenchBytecode
      (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem accessControlSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    accessControlSelWord I = sel := by
  apply u256_inj
  dsimp [accessControlSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem accessControlLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc j))
        (accessControlSelWord I) =
      if (accessControlLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem accessControlHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc j))
        (accessControlSelWord I) =
      if (accessControlHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem accessControlLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (accessControlLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc i))
        (accessControlSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = accessControlLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [accessControlLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [accessControlLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem accessControlHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (accessControlHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc i))
        (accessControlSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = accessControlHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [accessControlHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [accessControlHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem accessControlPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (accessControlLowSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat accessControlBenchBytecode accessControlSplitPc)
      (accessControlSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode accessControlLowFirstArmPc :=
      accessControlSelWord_eq_of_beq I hsz 0x01 0xff 0xc9 0xa7 _ (by decide)
        (by simpa [accessControlLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc 1) :=
      accessControlSelWord_eq_of_beq I hsz 0x24 0x8a 0x9c 0xa3 _ (by decide)
        (by simpa [accessControlLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc 2) :=
      accessControlSelWord_eq_of_beq I hsz 0x2f 0x2f 0xf1 0x5d _ (by decide)
        (by simpa [accessControlLowSelBytes] using hsel)
    rw [hword]; decide

theorem accessControlPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (accessControlHighSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat accessControlBenchBytecode accessControlSplitPc)
      (accessControlSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : accessControlSelWord I = armSelNat accessControlBenchBytecode accessControlSplitPc :=
      accessControlSelWord_eq_of_beq I hsz 0x36 0x56 0x8a 0xbe _ (by decide)
        (by simpa [accessControlHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc 1) :=
      accessControlSelWord_eq_of_beq I hsz 0x91 0xd1 0x48 0x54 _ (by decide)
        (by simpa [accessControlHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc 2) :=
      accessControlSelWord_eq_of_beq I hsz 0xa2 0x17 0xfd 0xdf _ (by decide)
        (by simpa [accessControlHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : accessControlSelWord I =
        armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc 3) :=
      accessControlSelWord_eq_of_beq I hsz 0xd5 0x47 0x74 0x1f _ (by decide)
        (by simpa [accessControlHighSelBytes] using hsel)
    rw [hword]; decide

/-! ## Dispatch reachability -/

theorem accessControlReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I)
        accessControlSplitPc [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed accessControlBenchBytecode accessControlSplitPc := by
    solc_dispatch_prefix
  simpa [accessControlSelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

theorem accessControlReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat accessControlBenchBytecode accessControlSplitPc)
      (accessControlSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc i))
        (accessControlSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J accessControlBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt accessControlBenchBytecode
        (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed accessControlBenchBytecode accessControlSplitPc := by
    solc_dispatch_prefix
  simpa [accessControlSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := accessControlBenchBytecode) (splitPc := accessControlSplitPc) (bodyPC := bodyPC)
      (i := i) hcode hwv hsz hsize hprefix (by jump_dest) accessControlSplitWellFormed
      (by simpa [accessControlSelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [accessControlHighFirstArmPc, accessControlSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          accessControlHighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [accessControlSelWord, solcSelectorWord, accessControlHighFirstArmPc,
          accessControlSplitPc, selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [accessControlSelWord, solcSelectorWord, accessControlHighFirstArmPc,
          accessControlSplitPc, selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [accessControlHighFirstArmPc, accessControlSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

theorem accessControlReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat accessControlBenchBytecode accessControlSplitPc)
      (accessControlSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc i))
        (accessControlSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J accessControlBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt accessControlBenchBytecode
        (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed accessControlBenchBytecode accessControlSplitPc := by
    solc_dispatch_prefix
  simpa [accessControlSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := accessControlBenchBytecode) (splitPc := accessControlSplitPc) (bodyPC := bodyPC)
      (i := i) hcode hwv hsz hsize hprefix (by jump_dest) accessControlSplitWellFormed
      (by simpa [accessControlSelWord, solcSelectorWord] using hpivot) (by jump_dest) (by decide)
      (fun j hj => by
        simpa [accessControlLowFirstArmPc, accessControlLowJumpdestPc, accessControlSplitPc,
          armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          accessControlLowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [accessControlSelWord, solcSelectorWord, accessControlLowFirstArmPc,
          accessControlLowJumpdestPc, accessControlSplitPc, armTgt, pushAt, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [accessControlSelWord, solcSelectorWord, accessControlLowFirstArmPc,
          accessControlLowJumpdestPc, accessControlSplitPc, armTgt, pushAt, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [accessControlLowFirstArmPc, accessControlLowJumpdestPc, accessControlSplitPc,
          armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

/-! ## Dispatch failures and global non-payable guard -/

theorem accessControlDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition, hasRoleTransition,
      renounceRoleTransition, revokeRoleTransition, supportsInterfaceTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, defaultAdminRoleSelectorBytes]; rfl
    · rw [selectorOf, getRoleAdminSelectorBytes]; rfl
    · rw [selectorOf, grantRoleSelectorBytes]; rfl
    · rw [selectorOf, hasRoleSelectorBytes]; rfl
    · rw [selectorOf, renounceRoleSelectorBytes]; rfl
    · rw [selectorOf, revokeRoleSelectorBytes]; rfl
    · rw [selectorOf, supportsInterfaceSelectorBytes]; rfl) h

theorem accessControlDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 7 → (accessControlSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes]
    simpa [accessControlSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, getRoleAdminSelectorBytes]
    simpa [accessControlSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, grantRoleSelectorBytes]
    simpa [accessControlSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, hasRoleSelectorBytes]
    simpa [accessControlSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, renounceRoleSelectorBytes]
    simpa [accessControlSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, revokeRoleSelectorBytes]
    simpa [accessControlSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, supportsInterfaceSelectorBytes]
    simpa [accessControlSelBytes] using hnm 6 (by omega)

theorem accessControlBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem accessControlX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt accessControlBenchBytecode)
    (opC := solcGuardTgtOp accessControlBenchBytecode)
    (wC := solcGuardTgtWidth accessControlBenchBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem accessControlX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt accessControlBenchBytecode)
    (opC := solcGuardTgtOp accessControlBenchBytecode)
    (wC := solcGuardTgtWidth accessControlBenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc accessControlBenchBytecode)
    (rtgt := solcCalldataRevertTgt accessControlBenchBytecode)
    (opR := solcCalldataRevertTgtOp accessControlBenchBytecode)
    (wR := solcCalldataRevertTgtWidth accessControlBenchBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem accessControlX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = accessControlBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 7 → (accessControlSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlLowFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [accessControlLowArmEq I hsz 0 (by omega)]
      have h := hnm 6 (by omega)
      have hfalse : (accessControlLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [accessControlLowSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
    · rw [accessControlLowArmEq I hsz 1 (by omega)]
      have h := hnm 1 (by omega)
      have hfalse : (accessControlLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [accessControlLowSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
    · rw [accessControlLowArmEq I hsz 2 (by omega)]
      have h := hnm 2 (by omega)
      have hfalse : (accessControlLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [accessControlLowSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat accessControlBenchBytecode
          (nthArmPc accessControlBenchBytecode accessControlHighFirstArmPc j))
        (accessControlSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [accessControlHighArmEq I hsz 0 (by omega)]
      have h := hnm 4 (by omega)
      have hfalse : (accessControlHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [accessControlHighSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
    · rw [accessControlHighArmEq I hsz 1 (by omega)]
      have h := hnm 3 (by omega)
      have hfalse : (accessControlHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [accessControlHighSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
    · rw [accessControlHighArmEq I hsz 2 (by omega)]
      have h := hnm 0 (by omega)
      have hfalse : (accessControlHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [accessControlHighSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
    · rw [accessControlHighArmEq I hsz 3 (by omega)]
      have h := hnm 5 (by omega)
      have hfalse : (accessControlHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [accessControlHighSelBytes, accessControlSelBytes] using h
      rw [hfalse]
      rfl
  obtain ⟨kS, CS, hsplit⟩ := accessControlReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat accessControlBenchBytecode accessControlSplitPc)
      (accessControlSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit accessControlSplitWellFormed hpivot (by simp)
    have h85 := h41
      |>.selectorArmNotTakenAuto (accessControlHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (accessControlHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (accessControlHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (accessControlHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
    have h85' : ∃ k C, RD accessControlBenchBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨85⟩ [accessControlSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [accessControlHighFirstArmPc, accessControlSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h85
    obtain ⟨_, _, h85rd⟩ := h85'
    exact h85rd.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h88 := RD.selectorSplitTakenAuto hsplit accessControlSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h89 := h88.jumpdest (by decide) (by simp)
    have h122 := h89
      |>.selectorArmNotTakenAuto (accessControlLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (accessControlLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (accessControlLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
    have h122' : ∃ k C, RD accessControlBenchBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨122⟩ [accessControlSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22, ?_⟩
      simpa [accessControlLowFirstArmPc, accessControlLowJumpdestPc, accessControlSplitPc,
        nthArmPc, selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc,
        selArmEqPc, selArmPush4Pc] using h122
    obtain ⟨_, _, h122rd⟩ := h122'
    have h123 := h122rd.jumpdest (by decide) (by simp)
    exact h123.revertStub (by decide) (by decide) (by decide) (by simp)

/-! ## Scalar return encodings -/

theorem boolTrueReturnEncodingAC :
    encodeReturnValue? boolTy (.bool true) = some (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  simpa [boolTy] using boolTrueReturnEncoding

theorem accessControlBytes32ReturnEncoding (w : UInt256) :
    encodeReturnValue? bytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  refine scalarReturnEncoding (t := .bytes ⟨31, by decide⟩) (w := w) (by native_decide) ?_ ?_
  · native_decide
  · simp [encodeABIValue?, hlen, zeroBytes]

end OpenZeppelinBench.AccessControl
