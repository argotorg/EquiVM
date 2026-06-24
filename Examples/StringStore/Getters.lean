import Examples.StringStore.Bytecode
import Examples.StringStore.Spec
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.SolmBody
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.Theory
import Mathlib.Tactic.IntervalCases

/-!
# StringStore — completed runtime/getter proof facts

This file contains the shared dispatch/Solm-side proof surface plus the runtime branches completed
so far: generic revert paths, `rawLength`, `historyLength`, and the zero-length `currentLength`
branch.  Future mutating-function proofs should live in modules above this one to keep these
completed facts cached.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- StringStore function selectors, in `stringStoreContract.transitions` order. -/
def stringStoreSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ -- set(string)
  | 1 => ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ -- appendToHistory(string)
  | 2 => ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ -- replaceFromHistory(uint256)
  | 3 => ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ -- dropLast()
  | 4 => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ -- clearCurrent()
  | 5 => ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ -- clearAll()
  | 6 => ⟨#[0x68, 0xb3, 0x91, 0x68]⟩ -- storeRaw(bytes)
  | 7 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ -- currentLength()
  | 8 => ⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ -- historyLength()
  | _ => ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ -- rawLength()

/-! ## Bytecode dispatcher shape -/

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev stringStoreSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- Low selector half, in bytecode arm order. -/
def stringStoreLowSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ -- replaceFromHistory(uint256)
  | 1 => ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ -- dropLast()
  | 2 => ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ -- set(string)
  | 3 => ⟨#[0x68, 0xb3, 0x91, 0x68]⟩ -- storeRaw(bytes)
  | _ => ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ -- rawLength()

/-- High selector half, in bytecode arm order. -/
def stringStoreHighSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ -- appendToHistory(string)
  | 1 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ -- currentLength()
  | 2 => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ -- clearCurrent()
  | 3 => ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ -- clearAll()
  | _ => ⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ -- historyLength()

/-- StringStore's binary-search selector split begins after the standard solc selector load. -/
abbrev stringStoreSplitPc : UInt256 := ⟨30⟩
/-- The high selector group falls through from the split to pc 41. -/
abbrev stringStoreHighFirstArmPc : UInt256 := ⟨41⟩
/-- The low selector group is reached by a taken split jump to this `JUMPDEST`. -/
abbrev stringStoreLowJumpdestPc : UInt256 := ⟨100⟩
/-- The low selector group begins after the `JUMPDEST` at pc 100. -/
abbrev stringStoreLowFirstArmPc : UInt256 := ⟨101⟩

theorem stringStoreSplitWellFormed :
    selectorSplitWellFormed stringStoreBytecode stringStoreSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem stringStoreHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed stringStoreBytecode
      (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem stringStoreLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed stringStoreBytecode
      (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `ByteArray` `==` reflects equality. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

theorem stringStoreSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : Nat) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    stringStoreSelWord I = sel := by
  apply u256_inj
  dsimp [stringStoreSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem stringStoreLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc j))
        (stringStoreSelWord I)
      = if (stringStoreLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem stringStoreHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc j))
        (stringStoreSelWord I)
      = if (stringStoreHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem stringStoreLowMatches {I : ExecutionEnv} (i : Nat) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (stringStoreLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc i))
        (stringStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = stringStoreLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [stringStoreLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [stringStoreLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem stringStoreHighMatches {I : ExecutionEnv} (i : Nat) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (stringStoreHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc i))
        (stringStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = stringStoreHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [stringStoreHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [stringStoreHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem stringStorePivotTaken {I : ExecutionEnv} (i : Nat) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (stringStoreLowSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat stringStoreBytecode stringStoreSplitPc) (stringStoreSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : stringStoreSelWord I = armSelNat stringStoreBytecode stringStoreLowFirstArmPc :=
      stringStoreSelWord_eq_of_beq I hsz 0x0f 0x76 0xd8 0xb4 _ (by decide)
        (by simpa [stringStoreLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc 1) :=
      stringStoreSelWord_eq_of_beq I hsz 0x4e 0x30 0x50 0x6f _ (by decide)
        (by simpa [stringStoreLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc 2) :=
      stringStoreSelWord_eq_of_beq I hsz 0x4e 0xd3 0x88 0x5e _ (by decide)
        (by simpa [stringStoreLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc 3) :=
      stringStoreSelWord_eq_of_beq I hsz 0x68 0xb3 0x91 0x68 _ (by decide)
        (by simpa [stringStoreLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc 4) :=
      stringStoreSelWord_eq_of_beq I hsz 0x72 0xc9 0xa7 0x6f _ (by decide)
        (by simpa [stringStoreLowSelBytes] using hsel)
    rw [hword]; decide

theorem stringStorePivotNotTaken {I : ExecutionEnv} (i : Nat) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (stringStoreHighSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat stringStoreBytecode stringStoreSplitPc) (stringStoreSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : stringStoreSelWord I = armSelNat stringStoreBytecode stringStoreSplitPc :=
      stringStoreSelWord_eq_of_beq I hsz 0x7d 0x4d 0x56 0x80 _ (by decide)
        (by simpa [stringStoreHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc 1) :=
      stringStoreSelWord_eq_of_beq I hsz 0xa3 0xd3 0x5f 0x36 _ (by decide)
        (by simpa [stringStoreHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc 2) :=
      stringStoreSelWord_eq_of_beq I hsz 0xa6 0xdf 0xa2 0x62 _ (by decide)
        (by simpa [stringStoreHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc 3) :=
      stringStoreSelWord_eq_of_beq I hsz 0xeb 0xb6 0x89 0xa1 _ (by decide)
        (by simpa [stringStoreHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : stringStoreSelWord I =
        armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc 4) :=
      stringStoreSelWord_eq_of_beq I hsz 0xf1 0x27 0x9c 0x8c _ (by decide)
        (by simpa [stringStoreHighSelBytes] using hsel)
    rw [hword]; decide

theorem stringStoreReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) stringStoreSplitPc
        [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed stringStoreBytecode stringStoreSplitPc := by
    solc_dispatch_prefix
  simpa [stringStoreSelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

theorem stringStoreReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : Nat) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat stringStoreBytecode stringStoreSplitPc)
      (stringStoreSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc i))
        (stringStoreSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J stringStoreBytecode 0).contains bodyPC = true)
    (hbody : armTgt stringStoreBytecode
        (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed stringStoreBytecode stringStoreSplitPc := by
    solc_dispatch_prefix
  simpa [stringStoreSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := stringStoreBytecode) (splitPc := stringStoreSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) stringStoreSplitWellFormed
      (by simpa [stringStoreSelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [stringStoreHighFirstArmPc, stringStoreSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          stringStoreHighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [stringStoreSelWord, solcSelectorWord, stringStoreHighFirstArmPc,
          stringStoreSplitPc, selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [stringStoreSelWord, solcSelectorWord, stringStoreHighFirstArmPc,
          stringStoreSplitPc, selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [stringStoreHighFirstArmPc, stringStoreSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

theorem stringStoreReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : Nat) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat stringStoreBytecode stringStoreSplitPc)
      (stringStoreSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc i))
        (stringStoreSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J stringStoreBytecode 0).contains bodyPC = true)
    (hbody : armTgt stringStoreBytecode
        (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed stringStoreBytecode stringStoreSplitPc := by
    solc_dispatch_prefix
  simpa [stringStoreSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := stringStoreBytecode) (splitPc := stringStoreSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) stringStoreSplitWellFormed
      (by simpa [stringStoreSelWord, solcSelectorWord] using hpivot) (by jump_dest) (by decide)
      (fun j hj => by
        simpa [stringStoreLowFirstArmPc, stringStoreLowJumpdestPc, stringStoreSplitPc, armTgt,
          pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          stringStoreLowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [stringStoreSelWord, solcSelectorWord, stringStoreLowFirstArmPc,
          stringStoreLowJumpdestPc, stringStoreSplitPc, armTgt, pushAt, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [stringStoreSelWord, solcSelectorWord, stringStoreLowFirstArmPc,
          stringStoreLowJumpdestPc, stringStoreSplitPc, armTgt, pushAt, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [stringStoreLowFirstArmPc, stringStoreLowJumpdestPc, stringStoreSplitPc, armTgt,
          pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

theorem stringStoreTransitions :
    stringStoreContract.transitions =
      [ setTransition, appendToHistoryTransition, replaceFromHistoryTransition, dropLastTransition,
        clearCurrentTransition, clearAllTransition, storeRawTransition, currentLengthGetter,
        historyLengthGetter, rawLengthGetter ] :=
  rfl

theorem stringStoreDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg stringStoreContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, stringStoreTransitions]
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t; rw [selectorOf, setSelectorBytes]; rfl
    · subst t; rw [selectorOf, appendToHistorySelectorBytes]; rfl
    · subst t; rw [selectorOf, replaceFromHistorySelectorBytes]; rfl
    · subst t; rw [selectorOf, dropLastSelectorBytes]; rfl
    · subst t; rw [selectorOf, clearCurrentSelectorBytes]; rfl
    · subst t; rw [selectorOf, clearAllSelectorBytes]; rfl
    · subst t; rw [selectorOf, storeRawSelectorBytes]; rfl
    · subst t; rw [selectorOf, currentLengthSelectorBytes]; rfl
    · subst t; rw [selectorOf, historyLengthSelectorBytes]; rfl
    · subst t; rw [selectorOf, rawLengthSelectorBytes]; rfl) h

theorem stringStoreDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 10 → (stringStoreSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg stringStoreContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, stringStoreTransitions]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  · subst t
    rw [selectorOf, setSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 0 (by omega)
  · subst t
    rw [selectorOf, appendToHistorySelectorBytes]
    simpa [stringStoreSelBytes] using hnm 1 (by omega)
  · subst t
    rw [selectorOf, replaceFromHistorySelectorBytes]
    simpa [stringStoreSelBytes] using hnm 2 (by omega)
  · subst t
    rw [selectorOf, dropLastSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 3 (by omega)
  · subst t
    rw [selectorOf, clearCurrentSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 4 (by omega)
  · subst t
    rw [selectorOf, clearAllSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 5 (by omega)
  · subst t
    rw [selectorOf, storeRawSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 6 (by omega)
  · subst t
    rw [selectorOf, currentLengthSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 7 (by omega)
  · subst t
    rw [selectorOf, historyLengthSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 8 (by omega)
  · subst t
    rw [selectorOf, rawLengthSelectorBytes]
    simpa [stringStoreSelBytes] using hnm 9 (by omega)

theorem stringStoreDecode_empty {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata [] [] I.calldata = some (∅ : Solm.Store) :=
  decodeCalldata_empty_ok hsz

/-! ## Shared runtime revert paths -/

/-- Every StringStore transition body reverts when the non-payable guard sees non-zero callvalue. -/
theorem stringStoreBodyReverts_nonPayable (t : TransitionDecl)
    (ht : t ∈ stringStoreContract.transitions) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm locals t.body .reverted := by
  simp [stringStoreContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-- EVM non-payable guard reverts when `callvalue ≠ 0`. -/
theorem stringStoreX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt stringStoreBytecode) (opC := solcGuardTgtOp stringStoreBytecode)
    (wC := solcGuardTgtWidth stringStoreBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- EVM calldata-size guard reverts when calldata is shorter than a selector. -/
theorem stringStoreX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt stringStoreBytecode) (opC := solcGuardTgtOp stringStoreBytecode)
    (wC := solcGuardTgtWidth stringStoreBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc stringStoreBytecode)
    (rtgt := solcCalldataRevertTgt stringStoreBytecode)
    (opR := solcCalldataRevertTgtOp stringStoreBytecode)
    (wR := solcCalldataRevertTgtWidth stringStoreBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

/-- With enough calldata for a selector but no selector match, StringStore's dispatcher reverts. -/
theorem stringStoreX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 10 → (stringStoreSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreLowFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hmiss : (stringStoreLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreLowSelBytes, stringStoreSelBytes] using hnm 2 (by omega)
      rw [stringStoreLowArmEq I hsz 0 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreLowSelBytes, stringStoreSelBytes] using hnm 3 (by omega)
      rw [stringStoreLowArmEq I hsz 1 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreLowSelBytes, stringStoreSelBytes] using hnm 0 (by omega)
      rw [stringStoreLowArmEq I hsz 2 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreLowSelBytes, stringStoreSelBytes] using hnm 6 (by omega)
      rw [stringStoreLowArmEq I hsz 3 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreLowSelBytes, stringStoreSelBytes] using hnm 9 (by omega)
      rw [stringStoreLowArmEq I hsz 4 (by omega), hmiss]; rfl
  have heqHigh0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat stringStoreBytecode (nthArmPc stringStoreBytecode stringStoreHighFirstArmPc j))
        (stringStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hmiss : (stringStoreHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreHighSelBytes, stringStoreSelBytes] using hnm 1 (by omega)
      rw [stringStoreHighArmEq I hsz 0 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreHighSelBytes, stringStoreSelBytes] using hnm 7 (by omega)
      rw [stringStoreHighArmEq I hsz 1 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreHighSelBytes, stringStoreSelBytes] using hnm 4 (by omega)
      rw [stringStoreHighArmEq I hsz 2 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreHighSelBytes, stringStoreSelBytes] using hnm 5 (by omega)
      rw [stringStoreHighArmEq I hsz 3 (by omega), hmiss]; rfl
    · have hmiss : (stringStoreHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [stringStoreHighSelBytes, stringStoreSelBytes] using hnm 8 (by omega)
      rw [stringStoreHighArmEq I hsz 4 (by omega), hmiss]; rfl
  obtain ⟨kS, CS, hsplit⟩ := stringStoreReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat stringStoreBytecode stringStoreSplitPc)
      (stringStoreSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit stringStoreSplitWellFormed hpivot (by simp)
    have h96 := h41
      |>.selectorArmNotTakenAuto (stringStoreHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreHighArmsWellFormed 4 (by omega))
          (heqHigh0 4 (by omega)) (by simp)
    have h96' : ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨96⟩
        [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [stringStoreHighFirstArmPc, stringStoreSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h96
    obtain ⟨_, _, h96rd⟩ := h96'
    have h156 := evm_run h96rd with [push2 ⟨156⟩, jump (by jump_dest)]
    have h157 := h156.jumpdest (by decide) (by simp)
    exact h157.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h100 := RD.selectorSplitTakenAuto hsplit stringStoreSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h101 := h100.jumpdest (by decide) (by simp)
    have h156 := h101
      |>.selectorArmNotTakenAuto (stringStoreLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreLowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (stringStoreLowArmsWellFormed 4 (by omega))
          (heqLow0 4 (by omega)) (by simp)
    have h156' : ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨156⟩
        [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [stringStoreLowFirstArmPc, stringStoreLowJumpdestPc, stringStoreSplitPc,
        nthArmPc, selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc,
        selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h156
    obtain ⟨_, _, h156rd⟩ := h156'
    have h157 := h156rd.jumpdest (by decide) (by simp)
    exact h157.revertStub (by decide) (by decide) (by decide) (by simp)

/-- `callvalue ≠ 0` implies both sides revert at the shared non-payable guard. -/
theorem stringStoreNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (stringStoreX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg stringStoreContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ stringStoreContract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (stringStoreBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector reverts before Solm dispatch. -/
theorem stringStoreShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (stringStoreX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (stringStoreDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches, so Solm dispatch fails and the EVM reverts. -/
theorem stringStoreNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 10 → (stringStoreSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (stringStoreX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (stringStoreDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (stringStoreX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch
      hcode (stringStoreDispatch_none_short hshort)

theorem stringStoreReachCurrentLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreHighMatches 1 (by omega) hsz hsel
  exact stringStoreReachHighBody 1 (by omega) ⟨412⟩ hcode hwv hsz hsize
    (stringStorePivotNotTaken 1 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachRawLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreLowMatches 4 (by omega) hsz hsel
  exact stringStoreReachLowBody 4 (by omega) ⟨334⟩ hcode hwv hsz hsize
    (stringStorePivotTaken 4 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem currentLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .string))
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem currentLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .string))
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ currentLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem historyLengthBodyReturns {evm : EVM.State} {n : Int}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm historyRef =
        .ok ({ base := "history", steps := [] }, .dynamicArray .string))
    (hlen : storageLocLoad evm (uint256Loc ⟨1⟩) = .int n) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ historyLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind]
      simp [stringStoreConfig_storage_history_length, hlen, pure])

theorem rawLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm rawRef =
        .ok ({ base := "raw", steps := [] }, .bytes))
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "raw" } = .ok n) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ rawLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem rawLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm rawRef =
        .ok ({ base := "raw", steps := [] }, .bytes))
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "raw" } = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ rawLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem currentLengthResolve (evm : EVM.State) :
    resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .string) := by
  simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreContract, storageDecls, stringSt, EvalResult.ofOption,
    EvalResult.bind, pure, bind]

theorem rawLengthResolve (evm : EVM.State) :
    resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm rawRef =
        .ok ({ base := "raw", steps := [] }, .bytes) := by
  simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreContract, storageDecls, bytesSt, EvalResult.ofOption,
    EvalResult.bind, pure, bind]

theorem currentLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm (some (.int n))) :=
  currentLengthBodyReturns hwv (currentLengthResolve evm) hlen

theorem currentLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ currentLengthGetter.body
      .reverted :=
  currentLengthBodyReverts hwv (currentLengthResolve evm) hlen

theorem rawLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "raw" } = .ok n) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ rawLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm (some (.int n))) :=
  rawLengthBodyReturns hwv (rawLengthResolve evm) hlen

theorem rawLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : bytesLikeLength? stringStoreConfig evm { base := "raw" } = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ rawLengthGetter.body
      .reverted :=
  rawLengthBodyReverts hwv (rawLengthResolve evm) hlen

/-! ## Solidity bytes/string length decoding -/

def solidityBytesIsLong (header : UInt256) : Bool :=
  UInt256.land header ⟨1⟩ != ⟨0⟩

def solidityBytesLengthWord (header : UInt256) : UInt256 :=
  let flag := UInt256.land header ⟨1⟩
  let rawLen := UInt256.div header ⟨2⟩
  if flag = ⟨0⟩ then UInt256.land rawLen ⟨127⟩ else rawLen

def solidityBytesLengthNat (header : UInt256) : Nat :=
  (solidityBytesLengthWord header).toNat

def solidityBytesLengthMalformed (header : UInt256) : Prop :=
  UInt256.sub (UInt256.land header ⟨1⟩)
    (UInt256.lt (solidityBytesLengthWord header) ⟨32⟩) = ⟨0⟩

instance (header : UInt256) : Decidable (solidityBytesLengthMalformed header) := by
  unfold solidityBytesLengthMalformed
  infer_instance

def stringStoreBytesHeaderWord (baseSlot : UInt256) (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bytesLikeLengthLoc baseSlot evm).slot

@[simp] theorem bytesLikeLengthLoc_slot (baseSlot : UInt256) (evm : EVM.State) :
    (bytesLikeLengthLoc baseSlot evm).slot = baseSlot := by
  unfold bytesLikeLengthLoc
  split <;> rfl

def rawLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def currentLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def solcPanicSelectorWord : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def solcPanic22Mem1 : ByteArray :=
  solcPanicSelectorWord.toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def solcPanic22Mem : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 solcPanic22Mem1 4 32

noncomputable def currentLengthZeroAllocMem : ByteArray :=
  (⟨160⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 64 32

noncomputable def currentLengthZeroMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 currentLengthZeroAllocMem 128 32

noncomputable def currentLengthZeroReturnMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 currentLengthZeroMem 160 32

def currentLengthAllocSize (len : UInt256) : UInt256 :=
  ⟨32⟩ + (((⟨31⟩ + len) / ⟨32⟩) * ⟨32⟩)

def currentLengthFreePtr (len : UInt256) : UInt256 :=
  ⟨128⟩ + currentLengthAllocSize len

noncomputable def currentLengthAllocMem (len : UInt256) : ByteArray :=
  (currentLengthFreePtr len).toByteArray.write 0 solcFreePtrMem 64 32

noncomputable def currentLengthMem (len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (currentLengthAllocMem len) 128 32

noncomputable def currentLengthShortReturnMem (len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (currentLengthMem len) 192 32

def currentLengthLongPayloadWord (header : UInt256) : UInt256 :=
  (header / ⟨256⟩) * ⟨256⟩

noncomputable def currentLengthLongMem (len header : UInt256) : ByteArray :=
  (currentLengthLongPayloadWord header).toByteArray.write 0 (currentLengthMem len) 160 32

noncomputable def currentLengthPayloadReturnMem (len header : UInt256) : ByteArray :=
  len.toByteArray.write 0 (currentLengthLongMem len header) 192 32

theorem toByteArray_extract_all (v : UInt256) :
    (UInt256.toByteArray v).extract 0 32 = UInt256.toByteArray v := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (Nat.le_of_eq (toByteArray_size v))

theorem currentLengthAllocMem_size (len : UInt256) : (currentLengthAllocMem len).size = 96 := by
  have hEq :
      currentLengthAllocMem len =
        solcFreePtrMem.extract 0 64 ++ UInt256.toByteArray (currentLengthFreePtr len) ++
          solcFreePtrMem.extract 96 solcFreePtrMem.size := by
    rw [currentLengthAllocMem,
      write32_eq (UInt256.toByteArray (currentLengthFreePtr len)) solcFreePtrMem 64
        (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; decide)]
    rw [toByteArray_extract_all]
  rw [hEq, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, solcFreePtrMem_size]
  omega

theorem currentLengthMem_size (len : UInt256) : (currentLengthMem len).size = 160 := by
  rw [currentLengthMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthAllocMem_size]; decide)
      (by rw [currentLengthAllocMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, currentLengthAllocMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthMem_read128 (len : UInt256) :
    (currentLengthMem len).readWithPadding 128 32 = UInt256.toByteArray len := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthMem_size len; omega),
    currentLengthMem,
    toByteArray_write_eq _ _ _
      (by rw [currentLengthAllocMem_size]; decide)
      (by rw [currentLengthAllocMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, currentLengthAllocMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem currentLengthAllocMem_read64 (len : UInt256) :
    (currentLengthAllocMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [currentLengthAllocMem]
  rw [write32_read_back (UInt256.toByteArray (currentLengthFreePtr len)) solcFreePtrMem 64
    (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem currentLengthMem_read64 (len : UInt256) :
    (currentLengthMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthMem_size len; omega),
    currentLengthMem,
    toByteArray_write_eq _ _ _
      (by rw [currentLengthAllocMem_size]; decide)
      (by rw [currentLengthAllocMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_left _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)]
        omega),
    extract_append_left _ _ _ _
      (by rw [currentLengthAllocMem_size]),
    ← readWithPadding_eq_extract _ _ (by have := currentLengthAllocMem_size len; omega),
    currentLengthAllocMem_read64]

theorem currentLengthMem_mload64 (len freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthMem len).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthMem len).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := freePtr)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, currentLengthMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      currentLengthMem_read64 len)

theorem currentLengthShortReturnMem_size (len : UInt256) :
    (currentLengthShortReturnMem len).size = 224 := by
  rw [currentLengthShortReturnMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthMem_size]; decide)
      (by rw [currentLengthMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, currentLengthMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthShortReturnMem_read64 (len : UInt256) :
    (currentLengthShortReturnMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthShortReturnMem_size len; omega),
    currentLengthShortReturnMem,
    toByteArray_write_eq _ _ _
      (by rw [currentLengthMem_size]; decide)
      (by rw [currentLengthMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_left _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthMem_size,
          zeroes_ofNat_size _ (by norm_num)]
        omega),
    extract_append_left _ _ _ _
      (by rw [currentLengthMem_size]; decide),
    ← readWithPadding_eq_extract _ _ (by have := currentLengthMem_size len; omega),
    currentLengthMem_read64]

theorem currentLengthShortReturnMem_mload64 (len freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthShortReturnMem len).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthShortReturnMem len).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7) (v := freePtr)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, currentLengthShortReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      currentLengthShortReturnMem_read64 len)

theorem currentLengthShortReturnMem_read192 (len : UInt256) :
    (currentLengthShortReturnMem len).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthShortReturnMem_size len; omega),
    currentLengthShortReturnMem,
    toByteArray_write_eq _ _ _
      (by rw [currentLengthMem_size]; decide)
      (by rw [currentLengthMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, currentLengthMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem currentLengthLongMem_read128 (len header : UInt256) :
    (currentLengthLongMem len header).readWithPadding 128 32 = UInt256.toByteArray len := by
  rw [currentLengthLongMem]
  rw [write32_read_below (UInt256.toByteArray (currentLengthLongPayloadWord header))
    (currentLengthMem len) 160 128
    (by rw [toByteArray_size])
    (by rw [currentLengthMem_size])
    (by decide)]
  exact currentLengthMem_read128 len

theorem currentLengthLongMem_size (len header : UInt256) :
    (currentLengthLongMem len header).size = 192 := by
  rw [currentLengthLongMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthMem_size])
      (by rw [currentLengthMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, currentLengthMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthLongMem_read64 (len header : UInt256) :
    (currentLengthLongMem len header).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [currentLengthLongMem]
  rw [write32_read_below (UInt256.toByteArray (currentLengthLongPayloadWord header))
    (currentLengthMem len) 160 64
    (by rw [toByteArray_size])
    (by rw [currentLengthMem_size])
    (by decide)]
  exact currentLengthMem_read64 len

theorem currentLengthLongMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthLongMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthLongMem len header).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := freePtr)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, currentLengthLongMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      currentLengthLongMem_read64 len header)

theorem currentLengthLongMem_mload128 (len header : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (currentLengthLongMem len header).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthLongMem len header).readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := len)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, currentLengthLongMem]
      rw [toByteArray_write_eq _ _ _ (by rw [currentLengthMem_size])
        (by rw [currentLengthMem_size]; exact lt_usize _ (by norm_num))]
      rw [ByteArray.size_append, ByteArray.size_append, currentLengthMem_size,
        zeroes_ofNat_size _ (by norm_num), toByteArray_size]
      decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      currentLengthLongMem_read128 len header)

theorem currentLengthPayloadReturnMem_size (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).size = 224 := by
  rw [currentLengthPayloadReturnMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthLongMem_size])
      (by rw [currentLengthLongMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, currentLengthLongMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthPayloadReturnMem_read64 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [currentLengthPayloadReturnMem]
  rw [write32_read_below (UInt256.toByteArray len) (currentLengthLongMem len header) 192 64
    (by rw [toByteArray_size])
    (by rw [currentLengthLongMem_size])
    (by decide)]
  exact currentLengthLongMem_read64 len header

theorem currentLengthPayloadReturnMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadReturnMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadReturnMem len header).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7) (v := freePtr)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        currentLengthPayloadReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      currentLengthPayloadReturnMem_read64 len header)

theorem currentLengthPayloadReturnMem_read192 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  rw [readWithPadding_eq_extract _ _ (by
      have := currentLengthPayloadReturnMem_size len header
      omega),
    currentLengthPayloadReturnMem,
    toByteArray_write_eq _ _ _
      (by rw [currentLengthLongMem_size])
      (by rw [currentLengthLongMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthLongMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, currentLengthLongMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem ult_ne_zero_toNat_lt {a b : UInt256} (h : UInt256.lt a b ≠ ⟨0⟩) :
    a.toNat < b.toNat := by
  by_contra hlt
  have hz : UInt256.lt a b = ⟨0⟩ := ult_zero (by omega)
  exact h hz

theorem currentLength_short_valid_lt32 {len : UInt256}
    (hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len.toNat < 32 := by
  have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
    intro hltZero
    exact hvalid0 (by simp [hltZero, UInt256.sub])
  have hlt := ult_ne_zero_toNat_lt hltNe
  simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hlt

theorem currentLength_notGt31_of_lt32 {len : UInt256} (hlt32 : len.toNat < 32) :
    UInt256.lt ⟨31⟩ len = ⟨0⟩ := by
  exact ult_zero (by
    rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    omega)

theorem currentLengthFreePtr_eq_192_of_short_nonzero {len : UInt256}
    (hnonzero : len ≠ ⟨0⟩) (hlt32 : len.toNat < 32) :
    currentLengthFreePtr len = ⟨192⟩ := by
  have hpos : 0 < len.toNat := by
    cases hzero : len.toNat
    · exact False.elim (hnonzero (uint256_toNat_eq_zero hzero))
    · omega
  have h31len :
      ((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat := by
    rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega)
  have hdivNat :
      (((⟨31⟩ : UInt256) + len) / ⟨32⟩).toNat = 1 := by
    change (((⟨31⟩ : UInt256) + len).toNat / 32) = 1
    rw [h31len]
    have hge : 32 ≤ 31 + len.toNat := by omega
    have hlt : 31 + len.toNat < 64 := by omega
    have hposDiv : 0 < (31 + len.toNat) / 32 := Nat.div_pos hge (by decide)
    have hltDiv : (31 + len.toNat) / 32 < 2 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    omega
  have hdiv :
      (((⟨31⟩ : UInt256) + len) / ⟨32⟩) = ⟨1⟩ := by
    apply u256_inj
    simpa [show (⟨1⟩ : UInt256).toNat = 1 from rfl] using hdivNat
  rw [currentLengthFreePtr, currentLengthAllocSize, hdiv]
  native_decide

theorem currentLengthZeroAllocMem_eq :
    currentLengthZeroAllocMem =
      solcFreePtrMem.extract 0 64 ++ UInt256.toByteArray ⟨160⟩ ++
        solcFreePtrMem.extract 96 solcFreePtrMem.size := by
  rw [currentLengthZeroAllocMem,
    write32_eq (UInt256.toByteArray ⟨160⟩) solcFreePtrMem 64
      (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem currentLengthZeroAllocMem_size : currentLengthZeroAllocMem.size = 96 := by
  rw [currentLengthZeroAllocMem_eq, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, solcFreePtrMem_size]
  omega

theorem currentLengthZeroAllocMem_read64 :
    currentLengthZeroAllocMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [currentLengthZeroAllocMem]
  rw [write32_read_back (UInt256.toByteArray ⟨160⟩) solcFreePtrMem 64
    (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem currentLengthZeroMem_eq :
    currentLengthZeroMem =
      (currentLengthZeroAllocMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++
        UInt256.toByteArray ⟨0⟩ := by
  rw [currentLengthZeroMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthZeroAllocMem_size]; decide)
      (by rw [currentLengthZeroAllocMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [currentLengthZeroAllocMem_size]

theorem currentLengthZeroMem_size : currentLengthZeroMem.size = 160 := by
  rw [currentLengthZeroMem_eq, ByteArray.size_append, ByteArray.size_append,
    currentLengthZeroAllocMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthZeroMem_read128 :
    currentLengthZeroMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthZeroMem_size; omega),
    currentLengthZeroMem_eq,
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthZeroAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, currentLengthZeroAllocMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem currentLengthZeroMem_read64 :
    currentLengthZeroMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthZeroMem_size; omega),
    currentLengthZeroMem_eq,
    extract_append_left _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthZeroAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)]
        omega),
    extract_append_left _ _ _ _
      (by rw [currentLengthZeroAllocMem_size]),
    ← readWithPadding_eq_extract _ _ (by have := currentLengthZeroAllocMem_size; omega),
    currentLengthZeroAllocMem_read64]

theorem currentLengthZeroMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨0⟩ : UInt256))
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, currentLengthZeroMem_size]; decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      currentLengthZeroMem_read128)

theorem currentLengthZeroMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, currentLengthZeroMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      currentLengthZeroMem_read64)

theorem currentLengthZeroReturnMem_eq :
    currentLengthZeroReturnMem =
      (currentLengthZeroMem ++ ffi.ByteArray.zeroes (USize.ofNat 0)) ++
        UInt256.toByteArray ⟨0⟩ := by
  rw [currentLengthZeroReturnMem,
    toByteArray_write_eq _ _ _ (by rw [currentLengthZeroMem_size])
      (by rw [currentLengthZeroMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [currentLengthZeroMem_size]

theorem currentLengthZeroReturnMem_size : currentLengthZeroReturnMem.size = 192 := by
  rw [currentLengthZeroReturnMem_eq, ByteArray.size_append, ByteArray.size_append,
    currentLengthZeroMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem currentLengthZeroReturnMem_read64 :
    currentLengthZeroReturnMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [currentLengthZeroReturnMem]
  rw [write32_read_below (UInt256.toByteArray ⟨0⟩) currentLengthZeroMem 160 64
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroMem_size])
    (by decide)]
  exact currentLengthZeroMem_read64

theorem currentLengthZeroReturnMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, currentLengthZeroReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      currentLengthZeroReturnMem_read64)

theorem currentLengthZeroReturnMem_read160 :
    currentLengthZeroReturnMem.readWithPadding 160 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := currentLengthZeroReturnMem_size; omega),
    currentLengthZeroReturnMem_eq,
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, currentLengthZeroMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, currentLengthZeroMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

/-! ## `historyLength()` runtime body support -/

def historyLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

theorem stringStoreStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0
          (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad uint256Loc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem historyLengthBodyReturnsWord (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ historyLengthGetter.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
  have hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm historyRef =
      .ok ({ base := "history", steps := [] }, .dynamicArray .string) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, historyRef,
      storageTypeAt?, stringStoreContract, storageDecls, stringSt, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have hlen :
      storageLocLoad evm (uint256Loc ⟨1⟩) =
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :=
    stringStoreStorageLocLoad_uint256 evm ⟨1⟩
  exact historyLengthBodyReturns hwv hresolve hlen

theorem historyLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem currentLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem rawLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem dropLastSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem clearCurrentSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem clearAllSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem stringStoreDispatch_historyLength {cd : ByteArray}
    (hsel : ((⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some historyLengthGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition, clearAllTransition, storeRawTransition,
      currentLengthGetter])
    (post := [rawLengthGetter]) rfl ?_
    (by rw [selectorOf, historyLengthSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes, hcd]; decide
  · rw [selectorOf, clearAllSelectorBytes, hcd]; decide
  · rw [selectorOf, storeRawSelectorBytes, hcd]; decide
  · rw [selectorOf, currentLengthSelectorBytes, hcd]; decide

theorem stringStoreDispatch_currentLength {cd : ByteArray}
    (hsel : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some currentLengthGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition, clearAllTransition, storeRawTransition])
    (post := [historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, currentLengthSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes, hcd]; decide
  · rw [selectorOf, clearAllSelectorBytes, hcd]; decide
  · rw [selectorOf, storeRawSelectorBytes, hcd]; decide

theorem stringStoreDispatch_rawLength {cd : ByteArray}
    (hsel : ((⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some rawLengthGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition, clearAllTransition, storeRawTransition,
      currentLengthGetter, historyLengthGetter])
    (post := []) rfl ?_
    (by rw [selectorOf, rawLengthSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes, hcd]; decide
  · rw [selectorOf, clearAllSelectorBytes, hcd]; decide
  · rw [selectorOf, storeRawSelectorBytes, hcd]; decide
  · rw [selectorOf, currentLengthSelectorBytes, hcd]; decide
  · rw [selectorOf, historyLengthSelectorBytes, hcd]; decide

theorem stringStoreDecode_historyLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (historyLengthGetter.params.map Param.name)
      (transitionSignature historyLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreDecode_currentLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (currentLengthGetter.params.map Param.name)
      (transitionSignature currentLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreDecode_rawLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (rawLengthGetter.params.map Param.name)
      (transitionSignature rawLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreDecode_dropLast {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (dropLastTransition.params.map Param.name)
      (transitionSignature dropLastTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreDecode_clearCurrent {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (clearCurrentTransition.params.map Param.name)
      (transitionSignature clearCurrentTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreDecode_clearAll {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (clearAllTransition.params.map Param.name)
      (transitionSignature clearAllTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stringStoreX_currentLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1910⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩,
        stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd412⟩ := hreach
  have rd1896 := evm_run rd412 with [
    jumpdest, push2 ⟨420⟩, push2 ⟨1896⟩, jump (by jump_dest)]
  have rd1901 := evm_run rd1896 with [
    jumpdest, push0, push0, push0, dup1]
  obtain ⟨_, _, rd1902₀⟩ := rd1901.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1902⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1902⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1902₀⟩
  exact ⟨_, _, evm_run rd1902 with [
    push2 ⟨1910⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩

theorem stringStoreX_rawLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [rawLengthHeaderWord σ I, ⟨1752⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd334⟩ := hreach
  have rd1738 := evm_run rd334 with [
    jumpdest, push2 ⟨342⟩, push2 ⟨1738⟩, jump (by jump_dest)]
  have rd1743 := evm_run rd1738 with [
    jumpdest, push0, push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd1744₀⟩ := rd1743.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [rawLengthHeaderWord σ I, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd1744₀⟩
  exact ⟨_, _, evm_run rd1744 with [
    push2 ⟨1752⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩

theorem stringStoreX_bytesLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_bytesLengthDecoderLongValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_bytesLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_bytesLengthDecoderShortValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_currentLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
      [UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨420⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact stringStoreX_bytesLengthDecoderLongValid
    (stringStoreX_currentLengthReachDecoder hreach) hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_currentLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
      [UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact stringStoreX_bytesLengthDecoderShortValid
    (stringStoreX_currentLengthReachDecoder hreach) hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_currentLengthZeroReachCopyDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hdecoded : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1954⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1910⟩ := hdecoded
  have rd1933 := evm_run rd1910 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 currentLengthZeroAllocMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd1943 := evm_run rd1933 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 currentLengthZeroMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd1946 := evm_run rd1943 with [dup1]
  obtain ⟨_, _, rd1946₀⟩ := rd1946.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1946'⟩ : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      [currentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1946₀⟩
  exact ⟨_, _, evm_run rd1946' with [
    push2 ⟨1954⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩

theorem stringStoreX_currentLengthReachCopyDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1954⟩, ⟨0⟩, ⟨160⟩, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1910⟩ := hdecoded
  have rd1933 := evm_run rd1910 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd1943 := evm_run rd1933 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd1946 := evm_run rd1943 with [dup1]
  obtain ⟨_, _, rd1946₀⟩ := rd1946.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1946'⟩ : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      [currentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [currentLengthHeaderWord, initState] using rd1946₀⟩
  exact ⟨_, _, evm_run rd1946' with [
    push2 ⟨1954⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩

theorem stringStoreX_currentLengthZeroReturnToWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1954⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [⟨0⟩, stringStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hdecoded := stringStoreX_bytesLengthDecoderShortValidMem
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1954₀⟩ := hdecoded
  obtain ⟨_, _, rd1954⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1954⟩
        [⟨0⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨420⟩, stringStoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1954₀⟩
  have rd1960 := evm_run rd1954 with [jumpdest, dup1, iszero, push2 ⟨2029⟩]
  have rd2029 := rd1960.jumpiT (by decide) (by decide) (by jump_dest) (by evm_ov)
  have rd2038 := evm_run rd2029 with [
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd2039 := evm_run rd2038 with [
    raw mload 0 ⟨0⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      currentLengthZeroMem_mload128
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2039 with [
    swap2, pop, pop, swap1, jump (by jump_dest)]⟩

theorem stringStoreX_currentLengthShortNonzeroReturnToWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1954⟩, ⟨0⟩, ⟨160⟩, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I]
      (currentLengthLongMem len (currentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  have hdecoded := stringStoreX_bytesLengthDecoderShortValidMem
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1954₀⟩ := hdecoded
  obtain ⟨_, _, rd1954⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1954⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨420⟩, stringStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hlen] using rd1954₀⟩
  have rd1960 := evm_run rd1954 with [jumpdest, dup1, iszero, push2 ⟨2029⟩]
  have rd1961 := rd1960.jumpiNT (by decide) (isZero_eq_zero_of_ne hnonzero) (by evm_ov)
  have rd1968 := evm_run rd1961 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1988⟩]
  have rd1969 := rd1968.jumpiNT (by decide) hnotGt31 (by evm_ov)
  have rd1976 := evm_run rd1969 with [push2 ⟨256⟩, dup1, dup4]
  obtain ⟨_, _, rd1976₀⟩ := rd1976.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1976'⟩ : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1975⟩
      [currentLengthHeaderWord σ I, ⟨256⟩, ⟨256⟩, len, ⟨0⟩, ⟨160⟩, len,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1976₀⟩
  have rd1983 := evm_run rd1976' with [
    div, mul, dup4,
    raw mstore 3 (currentLengthLongMem len (currentLengthHeaderWord σ I))
      (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2029 := evm_run rd1983 with [
    swap2, push1 ⟨32⟩, add, swap2, push2 ⟨2029⟩, jump (by jump_dest)]
  have rd2038 := evm_run rd2029 with [
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd2039 := evm_run rd2038 with [
    raw mload 0 len (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (currentLengthLongMem_mload128 len (currentLengthHeaderWord σ I))
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2039 with [
    swap2, pop, pop, swap1, jump (by jump_dest)]⟩

theorem stringStoreX_currentLengthZeroReturnFromWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [⟨0⟩, stringStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd420⟩ := hreach
  have rd2523 := evm_run rd420 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      currentLengthZeroMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨433⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542 := evm_run rd2517 with [
    jumpdest, dup3,
    raw mstore 3 currentLengthZeroReturnMem (UInt256.ofNat 6) (by decide)
      mem_cost
      (by rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd433 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd433 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      currentLengthZeroReturnMem_mload64
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨160⟩ : UInt256) + ⟨32⟩) ⟨160⟩).toNat = 32 from by decide,
          currentLengthZeroReturnMem_read160])
      (by evm_ov)]

theorem stringStoreX_currentLengthShortReturnFromWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I]
      (currentLengthLongMem len (currentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hfree : currentLengthFreePtr len = ⟨192⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd420⟩ := hreach
  have rd2523 := evm_run rd420 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (currentLengthLongMem_mload64 len (currentLengthHeaderWord σ I) ⟨192⟩ hfree)
      (by decide) (by evm_ov),
    push2 ⟨433⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542 := evm_run rd2517 with [
    jumpdest, dup3,
    raw mstore 3 (currentLengthPayloadReturnMem len (currentLengthHeaderWord σ I))
      (UInt256.ofNat 7) (by decide)
      mem_cost
      (by rw [show (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) = 192 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd433 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd433 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 7) (by decide)
      mem_cost
      (currentLengthPayloadReturnMem_mload64 len (currentLengthHeaderWord σ I) ⟨192⟩ hfree)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by decide)
      mem_cost
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨192⟩ : UInt256) + ⟨32⟩) ⟨192⟩).toNat = 32 from by decide,
          currentLengthPayloadReturnMem_read192])
      (by evm_ov)]

theorem stringStoreX_currentLengthZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd1910₀⟩ := stringStoreX_currentLengthDecoderShortValid hreach hflag hvalid
  have hdecoded :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
        [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1910₀⟩
  exact stringStoreX_currentLengthZeroReturnFromWrapper
    (stringStoreX_currentLengthZeroReturnToWrapper
      (stringStoreX_currentLengthZeroReachCopyDecoder hdecoded)
      hflag hvalid hzero)

theorem stringStoreX_currentLengthShortNonzeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩)
    (hfree : currentLengthFreePtr len = ⟨192⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1910₀⟩ := stringStoreX_currentLengthDecoderShortValid hreach hflag hvalid
  have hdecoded :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hlen] using rd1910₀⟩
  exact stringStoreX_currentLengthShortReturnFromWrapper
    (stringStoreX_currentLengthShortNonzeroReturnToWrapper
      (stringStoreX_currentLengthReachCopyDecoder hdecoded)
      hflag hvalid hlen hnonzero hnotGt31)
    hfree

theorem stringStoreX_rawLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [rawLengthHeaderWord σ I, ⟨1752⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1752⟩
      [UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest) (by evm_ov)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, jump (by jump_dest)]⟩

theorem stringStoreX_rawLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [rawLengthHeaderWord σ I, ⟨1752⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1752⟩
      [UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag (by evm_ov)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, jump (by jump_dest)]⟩

theorem stringStoreX_rawLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1752⟩
      [len, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1752⟩ := hdecoded
  have rd342 := evm_run rd1752 with [
    jumpdest, swap1, pop, swap1, pop, swap1, jump (by jump_dest)]
  have rd2523 := evm_run rd342 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨355⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542 := evm_run rd2517 with [
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem len) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (((⟨128⟩ : UInt256) + ⟨0⟩).toNat) = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd355 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd355 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 len)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

theorem stringStoreX_rawLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩)) := by
  exact stringStoreX_rawLengthReturnFromDecoded
    (stringStoreX_rawLengthDecoderLongValid
      (stringStoreX_rawLengthReachDecoder hreach) hflag hvalid)

theorem stringStoreX_rawLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact stringStoreX_rawLengthReturnFromDecoded
    (stringStoreX_rawLengthDecoderShortValid
      (stringStoreX_rawLengthReachDecoder hreach) hflag hvalid)

theorem stringStoreX_rawLengthMalformedPanic {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3223⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3223⟩ := hreach
  have rd3144 := evm_run rd3223 with [
    push2 ⟨3230⟩, push2 ⟨3144⟩, jump (by jump_dest)]
  have rd3145 := rd3144.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3178 := rd3145.pushConst solcPanicSelectorWord (width := 32)
    (op := Operation.POp.PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd3178 with [
    push0,
    raw mstore 0 solcPanic22Mem1 (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 solcPanic22Mem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by simp only [List.length_cons]; omega)]

theorem stringStoreX_rawLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := stringStoreX_rawLengthReachDecoder hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest) (by evm_ov)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad (by evm_ov)
  have hpanic : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3223⟩
      [UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩,
        UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩, rawLengthHeaderWord σ I,
        ⟨1752⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd3223'⟩
  exact stringStoreX_rawLengthMalformedPanic hpanic
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_rawLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨334⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := stringStoreX_rawLengthReachDecoder hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag (by evm_ov)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad (by evm_ov)
  have hpanic : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3223⟩
      [UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩,
        UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        rawLengthHeaderWord σ I, ⟨1752⟩, ⟨2⟩, ⟨0⟩, ⟨342⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd3223'⟩
  exact stringStoreX_rawLengthMalformedPanic hpanic
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_bytesLengthDecoderLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact stringStoreX_rawLengthMalformedPanic ⟨_, _, rd3223'⟩
    (by simp only [List.length_cons]; omega)

theorem stringStoreX_bytesLengthDecoderShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact stringStoreX_rawLengthMalformedPanic ⟨_, _, rd3223'⟩
    (by simp only [List.length_cons]; omega)

theorem stringStoreX_currentLengthDecoderLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact stringStoreX_bytesLengthDecoderLongMalformed
    (stringStoreX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_currentLengthDecoderShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact stringStoreX_bytesLengthDecoderShortMalformed
    (stringStoreX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem rawLengthHeaderWord_eq_of_accountMapEquiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    rawLengthHeaderWord σ_evm I = rawLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩

theorem currentLengthHeaderWord_eq_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    currentLengthHeaderWord σ_evm I = currentLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩

theorem stringStoreCurrentLengthLongMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := stringStoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_currentLength (I := I) hsz
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hbad]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact currentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_currentLengthDecoderLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreCurrentLengthShortMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := stringStoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_currentLength (I := I) hsz
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hbad0]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact currentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_currentLengthDecoderShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreCurrentLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthLongMalformedBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts hflag hbad

theorem stringStoreCurrentLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthShortMalformedBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts hflag hbad

theorem stringStoreCurrentLengthShortZeroValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := stringStoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_currentLength (I := I) hsz
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hvalidZero :
      UInt256.sub ⟨0⟩ (UInt256.lt ⟨0⟩ ⟨32⟩) ≠ ⟨0⟩ := by
    decide
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok 0 := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hzero, hvalidZero, pure]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int 0))) := by
    exact currentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_currentLengthZeroValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid hzero)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding ⟨0⟩))

theorem stringStoreCurrentLengthShortZeroValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthShortZeroValidBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts hflag hvalid hzero

theorem stringStoreCurrentLengthShortNonzeroValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := stringStoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_currentLength (I := I) hsz
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag, ← hlen] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have hlenRes :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok len.toNat := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, ← hlen, hvalid0, pure]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat len.toNat)))) := by
    exact currentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlenRes
  exact (stringStoreX_currentLengthShortNonzeroValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid hlen hnonzero hnotGt31 hfree)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding len))

theorem stringStoreCurrentLengthShortNonzeroValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthShortNonzeroValidBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts hflag hvalid hlen hnonzero

theorem stringStoreRawLengthLongValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := rawLengthSelector_size hsel
  have hd := stringStoreDispatch_rawLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_rawLength (I := I) hsz
  have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [rawLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      rawLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "raw" } =
          .ok (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hvalid, pure]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        rawLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat
            (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact rawLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_rawLengthLongValid (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem stringStoreRawLengthShortValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := rawLengthSelector_size hsel
  have hd := stringStoreDispatch_rawLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_rawLength (I := I) hsz
  have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [rawLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      rawLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "raw" } =
          .ok (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hvalid0, pure]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        rawLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat
            (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact rawLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_rawLengthShortValid (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem stringStoreRawLengthLongMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := rawLengthSelector_size hsel
  have hd := stringStoreDispatch_rawLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_rawLength (I := I) hsz
  have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [rawLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      rawLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "raw" } =
          .revert := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hbad]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        rawLengthGetter.body .reverted := by
    exact rawLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_rawLengthLongMalformed (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreRawLengthShortMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := rawLengthSelector_size hsel
  have hd := stringStoreDispatch_rawLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_rawLength (I := I) hsz
  have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [rawLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      rawLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨2⟩ = rawLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "raw" } =
          .revert := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hbad0]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        rawLengthGetter.body .reverted := by
    exact rawLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (stringStoreX_rawLengthShortMalformed (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreRawLengthBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨334⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact stringStoreRawLengthShortValidBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreRawLengthShortMalformedBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact stringStoreRawLengthLongValidBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreRawLengthLongMalformedBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hbad

theorem stringStoreRawLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x72, 0xc9, 0xa7, 0x6f]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreRawLengthBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachRawLength (g := Sat256.ofUInt256 g) hcode hwv
      (rawLengthSelector_size hsel) hsize hsel)
    hAccounts

set_option maxHeartbeats 800000 in
theorem stringStoreX_historyLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨482⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (historyLengthWord σ I)) := by
  obtain ⟨_, _, rd482⟩ := hreach
  have rd2186 := evm_run rd482 with [
    jumpdest, push2 ⟨490⟩, push2 ⟨2186⟩, jump (by jump_dest)]
  have rd2191 := evm_run rd2186 with [
    jumpdest, push0, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd2192₀⟩ := rd2191.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2192⟩ :
      ∃ k C, RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2192⟩
        [historyLengthWord σ I, ⟨1⟩, ⟨0⟩, ⟨490⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [historyLengthWord, initState] using rd2192₀⟩
  have rd490 := evm_run rd2192 with [
    swap1, pop, swap1, pop, swap1, jump (by jump_dest)]
  have rd2523 := evm_run rd490 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨503⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542 := evm_run rd2517 with [
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem (historyLengthWord σ I)) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (((⟨128⟩ : UInt256) + ⟨0⟩).toNat) = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd503 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd503 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (historyLengthWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (historyLengthWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

theorem stringStoreHistoryLengthBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨482⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have hsel' : ((⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := historyLengthSelector_size hsel
  have hd := stringStoreDispatch_historyLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_historyLength (I := I) hsz
  have hword : historyLengthWord σ_evm I = historyLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        historyLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (historyLengthWord σ_solm I).toNat)))) := by
    simpa [historyLengthWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      historyLengthBodyReturnsWord
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  exact (stringStoreX_historyLength (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (historyLengthWord σ_evm I)))

theorem stringStoreHistoryLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xf1, 0x27, 0x9c, 0x8c]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreHistoryLengthBodyCore hcode hsize hperm hwv hsel
    (stringStoreReachHighBody 4 (by omega) ⟨482⟩ hcode hwv
      (historyLengthSelector_size hsel) hsize
      (stringStorePivotNotTaken 4 (by omega) (historyLengthSelector_size hsel) hsel)
      (stringStoreHighMatches 4 (by omega) (historyLengthSelector_size hsel) hsel).1
      (stringStoreHighMatches 4 (by omega) (historyLengthSelector_size hsel) hsel).2
      (by jump_dest) (by decide))
    hAccounts

end StringStore
