import Reasoning.ABIComposite
import Reasoning.SolcRoutines
import Benchmarks.Dss.Vow.Selectors
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Vow shared proof foundation

This file contains contract-wide selector, dispatch-failure, and global revert facts used by the
top-level runtime proof and the per-function body proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev vowSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def vowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩  -- Ash()
  | 1 => ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩  -- Sin()
  | 2 => ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩  -- bump()
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 5 => ⟨#[0xe4, 0x33, 0x05, 0x45]⟩  -- dump()
  | 6 => ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩  -- fess(uint256)
  | 7 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 8 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩  -- file(bytes32,address)
  | 9 => ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩  -- flap()
  | 10 => ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ -- flapper()
  | 11 => ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ -- flog(uint256)
  | 12 => ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ -- flop()
  | 13 => ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ -- flopper()
  | 14 => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ -- heal(uint256)
  | 15 => ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ -- hump()
  | 16 => ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ -- kiss(uint256)
  | 17 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 18 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 19 => ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ -- sin(uint256)
  | 20 => ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩ -- sump()
  | 21 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 22 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)

/-! ## Dispatcher constants and prefix reachability -/

abbrev vowRootSplitPc : UInt256 := ⟨32⟩
abbrev vowHighSplitPc : UInt256 := ⟨43⟩
abbrev vowHighHighFirstArmPc : UInt256 := ⟨54⟩
abbrev vowHighLowJumpdestPc : UInt256 := ⟨124⟩
abbrev vowHighLowFirstArmPc : UInt256 := ⟨125⟩
abbrev vowLowJumpdestPc : UInt256 := ⟨195⟩
abbrev vowLowSplitPc : UInt256 := ⟨196⟩
abbrev vowLowHighFirstArmPc : UInt256 := ⟨207⟩
abbrev vowLowLowJumpdestPc : UInt256 := ⟨277⟩
abbrev vowLowLowFirstArmPc : UInt256 := ⟨278⟩
abbrev vowDispatchBodyPc : UInt256 := ⟨18⟩
abbrev vowSelectorLoadPc : UInt256 := ⟨26⟩
abbrev vowDispatchRevertPc : UInt256 := ⟨344⟩

def vowLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ -- flap()
  | 1 => ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ -- hump()
  | 2 => ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ -- kiss(uint256)
  | 3 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 4 => ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩ -- Ash()
  | _ => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩  -- vat()

def vowLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ -- flopper()
  | 1 => ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ -- flapper()
  | 2 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | 3 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 4 => ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩ -- bump()
  | _ => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()

def vowHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩ -- fess(uint256)
  | 1 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ -- flop()
  | 4 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩  -- sump()

def vowHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ -- sin(uint256)
  | 1 => ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩ -- Sin()
  | 2 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 3 => ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ -- flog(uint256)
  | 4 => ⟨#[0xe4, 0x33, 0x05, 0x45]⟩ -- dump()
  | _ => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩  -- heal(uint256)


theorem vowSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    vowSelWord I = sel := by
  simpa [vowSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem vowRootSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vowHighSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vowLowSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem vowLowLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowLowHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowHighLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowHighHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem vowLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) =
      if (vowLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) =
      if (vowLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) =
      if (vowHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) =
      if (vowHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowReachRootSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowRootSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  simpa [vowRootSplitPc, vowSelWord] using
    solcLegacyDispatchReachSelector (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := vowBytecode)
      (bodyPc := vowDispatchBodyPc) (loadPc := vowSelectorLoadPc)
      (firstPc := vowRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := vowDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem vowReachLowSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowLowSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vowReachRootSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h195 : RD vowBytecode I g (initState σ σ₀ g A I)
      (armTgt vowBytecode vowRootSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vowRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h196 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowLowSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vowLowSplitPc, vowLowJumpdestPc, vowRootSplitPc, armTgt, pushAt]
      using h195.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h196⟩

theorem vowReachHighSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowHighSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vowReachRootSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowHighSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k32 + 5) (C32 + 22) := by
    simpa [vowHighSplitPc, vowRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vowRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem vowReachLowLowFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowLowLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k196, C196, h196⟩ :=
    vowReachLowSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h277 : RD vowBytecode I g (initState σ σ₀ g A I)
      (armTgt vowBytecode vowLowSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ (k196 + 5) (C196 + 22) :=
    RD.selectorSplitTakenAuto h196 vowLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h278 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowLowLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k196 + 5 + 1) (C196 + 22 + 1) := by
    simpa [vowLowLowFirstArmPc, vowLowLowJumpdestPc, vowLowSplitPc, armTgt, pushAt]
      using h277.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h278⟩

theorem vowReachLowHighFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowLowHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k196, C196, h196⟩ :=
    vowReachLowSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h207 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowLowHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k196 + 5) (C196 + 22) := by
    simpa [vowLowHighFirstArmPc, vowLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h196 vowLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h207⟩

theorem vowReachHighLowFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowHighLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k43, C43, h43⟩ :=
    vowReachHighSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h124 : RD vowBytecode I g (initState σ σ₀ g A I)
      (armTgt vowBytecode vowHighSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 vowHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h125 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowHighLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [vowHighLowFirstArmPc, vowHighLowJumpdestPc, vowHighSplitPc, armTgt, pushAt]
      using h124.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h125⟩

theorem vowReachHighHighFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        vowHighHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k43, C43, h43⟩ :=
    vowReachHighSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD vowBytecode I g (initState σ σ₀ g A I)
      vowHighHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5) (C43 + 22) := by
    simpa [vowHighHighFirstArmPc, vowHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 vowHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

theorem vowReachLowLowBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachLowLowFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowLowLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachLowHighBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachLowHighFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowLowHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachHighLowBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachHighLowFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowHighLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachHighHighBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachHighHighFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowHighHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowJumpToNoMatchRevert {σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD vowBytecode I g (initState σ σ₀ g A I) pc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hpush : decode vowBytecode pc = some (.Push .PUSH2, some (vowDispatchRevertPc, 2)))
    (hjump : decode vowBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h344 := h.push2 vowDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vowLowLowNoMatchRevert {σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState σ σ₀ g A I) vowLowLowFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h344 := h
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vowLowHighNoMatchRevert {σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState σ σ₀ g A I) vowLowHighFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h273 := h
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h273 (by native_decide) (by native_decide)

theorem vowHighLowNoMatchRevert {σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState σ σ₀ g A I) vowHighLowFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h191 := h
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h191 (by native_decide) (by native_decide)

theorem vowHighHighNoMatchRevert {σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState σ σ₀ g A I) vowHighHighFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h120 := h
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h120 (by native_decide) (by native_decide)

theorem vowX_noMatch {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 24 → (vowSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have heqLowLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (vowLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (vowLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (vowLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (vowLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 4 (by omega)]
      have hfalse : (vowLowLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 5 (by omega)]
      have hfalse : (vowLowLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 21 (by omega)
      rw [hfalse]; rfl
  have heqLowHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (vowLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (vowLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (vowLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 22 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (vowLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 4 (by omega)]
      have hfalse : (vowLowHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 5 (by omega)]
      have hfalse : (vowLowHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (vowHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (vowHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (vowHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (vowHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 4 (by omega)]
      have hfalse : (vowHighLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 23 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 5 (by omega)]
      have hfalse : (vowHighLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 20 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (vowHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (vowHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (vowHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (vowHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 4 (by omega)]
      have hfalse : (vowHighHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 5 (by omega)]
      have hfalse : (vowHighHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩
  · by_cases hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        vowReachLowLowFirstArm (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
      exact vowLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        vowReachLowHighFirstArm (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow0
      exact vowLowHighNoMatchRevert hfirst heqLowHigh
  · have hroot0 : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        vowReachHighLowFirstArm (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh
      exact vowHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 :
          UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        vowReachHighHighFirstArm (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0
      exact vowHighHighNoMatchRevert hfirst heqHighHigh

/-! ## Simple storage getter cores -/

theorem vowAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_address_offset0 evm slot))

theorem vowUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem vowAddressGetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = vowBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf vowBytecode entry ⟨465⟩ routine)
    (hgetter : solcAddressSlotGetterWf vowBytecode routine slot)
    (hroutine : (D_J vowBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (solcAddressSlotWord slot σ I).toNat))]))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcAddressSlotWord slot σ I))
        (some [(.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [solcAddressSlotWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWordAt slot σ I)))
  have hret := RD.solcAddressGetterExternal (code := vowBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨465⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcAddressSlotWord slot σ I)) := by
    simpa [solcAddressSlotWord, solcSlotWordAt] using hret
  exact hret'.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vowUint256GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = vowBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf vowBytecode entry ⟨357⟩ routine)
    (hgetter : solcWordSlotGetterWf vowBytecode routine slot)
    (hroutine : (D_J vowBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal (code := vowBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨357⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vowDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition,
      flapTransition, flapperTransition, flogTransition, flopTransition,
      flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes,
        flapperSelectorBytes, flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes,
        healSelectorBytes, humpSelectorBytes, kissSelectorBytes, liveSelectorBytes,
        relySelectorBytes, sinSelectorBytes, sumpSelectorBytes, vatSelectorBytes,
        waitSelectorBytes, wardsSelectorBytes]
      native_decide) h

theorem vowDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 24 → (vowSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, AshSelectorBytes]
    simpa [vowSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, SinSelectorBytes]
    simpa [vowSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, bumpSelectorBytes]
    simpa [vowSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [vowSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [vowSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, dumpSelectorBytes]
    simpa [vowSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fessSelectorBytes]
    simpa [vowSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [vowSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [vowSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, flapSelectorBytes]
    simpa [vowSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, flapperSelectorBytes]
    simpa [vowSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, flogSelectorBytes]
    simpa [vowSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, flopSelectorBytes]
    simpa [vowSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, flopperSelectorBytes]
    simpa [vowSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, healSelectorBytes]
    simpa [vowSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, humpSelectorBytes]
    simpa [vowSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, kissSelectorBytes]
    simpa [vowSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [vowSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [vowSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, sinSelectorBytes]
    simpa [vowSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, sumpSelectorBytes]
    simpa [vowSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [vowSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, waitSelectorBytes]
    simpa [vowSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [vowSelBytes] using hnm 23 (by omega)

theorem vowBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem vowX_callvalue_ne {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem vowX_short {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev vowBytecode g (initState σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt vowBytecode)
    (opC := solcGuardTgtOp vowBytecode)
    (wC := solcGuardTgtWidth vowBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h344 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 ⟨344⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

end Benchmarks.Dss.Vow
