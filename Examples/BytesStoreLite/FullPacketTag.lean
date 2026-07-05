import Examples.BytesStoreLite.Dispatch
import Examples.BytesStoreLite.StorageReadbackFacts
import Examples.BytesStoreLite.CoreGetters
import Examples.BytesStoreLite.CoreSetOldLong
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Reasoning.Theory
import Mathlib.Tactic.IntervalCases

/-!
# BytesStoreLite — full-runtime `packetTag()` slice

This file starts the optimized full-contract runtime proof with the simplest branch:
`packetTag()`, a scalar `uint256` getter at storage slot 3.  The dispatcher proof follows the
binary-search selector tree emitted by solc for the 15-function contract.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev bytesStoreLiteSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-! ## Dispatcher path for `packetTag()` -/

abbrev bytesStoreLiteSplitPc : UInt256 := ⟨30⟩
abbrev bytesStoreLiteHighSplitPc : UInt256 := ⟨41⟩
abbrev bytesStoreLiteHighFirstArmPc : UInt256 := ⟨52⟩
abbrev bytesStoreLiteMidLowJumpdestPc : UInt256 := ⟨99⟩
abbrev bytesStoreLiteMidLowFirstArmPc : UInt256 := ⟨100⟩
abbrev bytesStoreLiteRootLowJumpdestPc : UInt256 := ⟨147⟩
abbrev bytesStoreLiteLowSplitPc : UInt256 := ⟨148⟩
abbrev bytesStoreLiteLowFallthroughFirstArmPc : UInt256 := ⟨159⟩
abbrev bytesStoreLiteLowTakenJumpdestPc : UInt256 := ⟨206⟩
abbrev bytesStoreLiteLowTakenFirstArmPc : UInt256 := ⟨207⟩

def bytesStoreLiteMidLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩
  | 1 => ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩
  | 2 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩
  | _ => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩

def bytesStoreLiteHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩
  | 1 => ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩
  | 2 => ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩
  | _ => ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩

def bytesStoreLiteLowFallthroughSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩
  | 1 => ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩
  | 2 => ⟨#[0x39, 0x1d, 0x72, 0x80]⟩
  | _ => ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩

def bytesStoreLiteLowTakenSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x03, 0x99, 0x32, 0x1e]⟩
  | 1 => ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩
  | _ => ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩

theorem bytesStoreLiteSplitWellFormed :
    selectorSplitWellFormed bytesStoreLiteBytecode bytesStoreLiteSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreLiteHighSplitWellFormed :
    selectorSplitWellFormed bytesStoreLiteBytecode bytesStoreLiteHighSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreLiteLowSplitWellFormed :
    selectorSplitWellFormed bytesStoreLiteBytecode bytesStoreLiteLowSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreLiteHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLiteMidLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLiteLowFallthroughArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLiteLowTakenArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLiteSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    bytesStoreLiteSelWord I = sel := by
  apply u256_inj
  dsimp [bytesStoreLiteSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem bytesStoreLiteMidLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc j))
        (bytesStoreLiteSelWord I) =
      if (bytesStoreLiteMidLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLiteHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc j))
        (bytesStoreLiteSelWord I) =
      if (bytesStoreLiteHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLiteLowFallthroughArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc j))
        (bytesStoreLiteSelWord I) =
      if (bytesStoreLiteLowFallthroughSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLiteLowTakenArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc j))
        (bytesStoreLiteSelWord I) =
      if (bytesStoreLiteLowTakenSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLiteMidLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLiteMidLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc i))
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLiteMidLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLiteMidLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLiteMidLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLiteHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLiteHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc i))
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLiteHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLiteHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLiteHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLiteLowFallthroughMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLiteLowFallthroughSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc i))
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLiteLowFallthroughSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLiteLowFallthroughArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLiteLowFallthroughArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLiteLowTakenMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLiteLowTakenSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc i))
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLiteLowTakenSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLiteLowTakenArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLiteLowTakenArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLiteSetFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I = ⟨0x0399321e⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x03 0x99 0x32 0x1e _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteSetSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteLowSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I = ⟨0x0399321e⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x03 0x99 0x32 0x1e _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePacketTagFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2570979984⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x99 0x3e 0x0a 0x90 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePacketTagSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2570979984⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x99 0x3e 0x0a 0x90 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteCurrentLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2748538678⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xa3 0xd3 0x5f 0x36 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteCurrentLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2748538678⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xa3 0xd3 0x5f 0x36 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteClearCurrentFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2799673954⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xa6 0xdf 0xa2 0x62 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteClearCurrentSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨2799673954⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xa6 0xdf 0xa2 0x62 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePushChunkFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3037513900⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xb5 0x0c 0xc8 0xac _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePushChunkSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3037513900⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xb5 0x0c 0xc8 0xac _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePacketLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3038302916⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xb5 0x18 0xd2 0xc4 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLitePacketLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3038302916⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xb5 0x18 0xd2 0xc4 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteMappedLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨958231168⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x39 0x1d 0x72 0x80 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteMappedLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteLowSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨958231168⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0x39 0x1d 0x72 0x80 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteChunkLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3904740085⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xe8 0xbd 0x9a 0xf5 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteChunkLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreLiteSelWord I =
      ⟨3904740085⟩ :=
    bytesStoreLiteSelWord_eq_of_beq I hsz 0xe8 0xbd 0x9a 0xf5 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreLiteSolcDispatchPrefix :
    solcDispatchPrefixWellFormed bytesStoreLiteBytecode bytesStoreLiteSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreLiteSplitNextPc :
    selArmNextPc bytesStoreLiteSplitPc
      (armTgtWidth bytesStoreLiteBytecode bytesStoreLiteSplitPc) =
    bytesStoreLiteHighSplitPc := by
  native_decide

theorem bytesStoreLiteHighSplitTgt :
    armTgt bytesStoreLiteBytecode bytesStoreLiteHighSplitPc =
    bytesStoreLiteMidLowJumpdestPc := by
  native_decide

theorem bytesStoreLiteHighSplitNextPc :
    selArmNextPc bytesStoreLiteHighSplitPc
      (armTgtWidth bytesStoreLiteBytecode bytesStoreLiteHighSplitPc) =
    bytesStoreLiteHighFirstArmPc := by
  native_decide

theorem bytesStoreLiteSplitTgt :
    armTgt bytesStoreLiteBytecode bytesStoreLiteSplitPc =
    bytesStoreLiteRootLowJumpdestPc := by
  native_decide

theorem bytesStoreLiteLowSplitNextPc :
    selArmNextPc bytesStoreLiteLowSplitPc
      (armTgtWidth bytesStoreLiteBytecode bytesStoreLiteLowSplitPc) =
    bytesStoreLiteLowFallthroughFirstArmPc := by
  native_decide

theorem bytesStoreLiteLowSplitTgt :
    armTgt bytesStoreLiteBytecode bytesStoreLiteLowSplitPc =
    bytesStoreLiteLowTakenJumpdestPc := by
  native_decide

theorem bytesStoreLiteHighArmsEnd :
    nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc 4 = ⟨96⟩ := by
  native_decide

theorem bytesStoreLiteMidLowArmsEnd :
    nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc 4 = ⟨144⟩ := by
  native_decide

theorem bytesStoreLiteLowFallthroughArmsEnd :
    nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 4 = ⟨203⟩ := by
  native_decide

theorem bytesStoreLiteLowTakenArmsEnd :
    nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 3 = ⟨240⟩ := by
  native_decide

theorem bytesStoreLiteReachPacketTag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePacketTagFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePacketTagSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteMidLowFirstArmPc, bytesStoreLiteMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteMidLowMatches 1 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨433⟩ 1 hfirstRD
    (fun j hj => bytesStoreLiteMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachCurrentLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨441⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteCurrentLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteCurrentLengthSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteMidLowFirstArmPc, bytesStoreLiteMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteMidLowMatches 2 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨441⟩ 2 hfirstRD
    (fun j hj => bytesStoreLiteMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachClearCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨449⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteClearCurrentFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteClearCurrentSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteMidLowFirstArmPc, bytesStoreLiteMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteMidLowMatches 3 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨449⟩ 3 hfirstRD
    (fun j hj => bytesStoreLiteMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachPushChunk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨457⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePushChunkFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePushChunkSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteHighMatches 0 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨457⟩ 0 hfirstRD
    (fun j hj => bytesStoreLiteHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachPacketLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨476⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePacketLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLitePacketLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteHighMatches 1 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨476⟩ 1 hfirstRD
    (fun j hj => bytesStoreLiteHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachChunkLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨503⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteChunkLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteChunkLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteHighMatches 3 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨503⟩ 3 hfirstRD
    (fun j hj => bytesStoreLiteHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachMappedLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨376⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteRootLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteMappedLengthFirstPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteLowSplitPc, bytesStoreLiteRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowFallthroughFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hlowSplit bytesStoreLiteLowSplitWellFormed
        (by
          simpa [bytesStoreLiteSelWord, solcSelectorWord] using
            bytesStoreLiteMappedLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteLowFallthroughMatches 2 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteLowFallthroughSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨376⟩ 2 hfirstRD
    (fun j hj => bytesStoreLiteLowFallthroughArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreLiteReachSet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 0))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteRootLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreLiteSplitWellFormed
        (bytesStoreLiteSetFirstPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteLowSplitPc, bytesStoreLiteRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hlowTakenJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowTakenJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hlowSplit bytesStoreLiteLowSplitWellFormed
        (bytesStoreLiteSetSecondPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitTgt] using hstep
  obtain ⟨kT, CT, hlowTakenJdRD⟩ := hlowTakenJd
  have hfirst : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowTakenFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kT + 1, CT + 1, ?_⟩
    simpa [bytesStoreLiteLowTakenFirstArmPc, bytesStoreLiteLowTakenJumpdestPc] using
      hlowTakenJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLiteLowTakenMatches 0 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteLowTakenSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 0))
    0 hfirstRD
    (fun j hj => bytesStoreLiteLowTakenArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) rfl (by simp)

theorem bytesStoreLiteReachHighArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    (hsel : (bytesStoreLiteHighSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc i))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        hfirst (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have harm0 : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        hsecond (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := harm0
  rcases bytesStoreLiteHighMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLiteHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreLiteReachMidLowArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩)
    (hsel : (bytesStoreLiteMidLowSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc i))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed
        hfirst (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hmidJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreLiteHighSplitWellFormed
        hsecond (by native_decide) (by simp)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hmidJdRD⟩ := hmidJd
  have hfirstArm : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteMidLowFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteMidLowFirstArmPc, bytesStoreLiteMidLowJumpdestPc] using
      hmidJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreLiteMidLowMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLiteMidLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreLiteReachLowFallthroughArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteLowSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩)
    (hsel : (bytesStoreLiteLowFallthroughSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc i))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteRootLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreLiteSplitWellFormed
        hfirst (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteLowSplitPc, bytesStoreLiteRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hfirstArm : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowFallthroughFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hlowSplit bytesStoreLiteLowSplitWellFormed
        hsecond (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreLiteLowFallthroughMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLiteLowFallthroughArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreLiteReachLowTakenArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 3)
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteLowSplitPc)
        (bytesStoreLiteSelWord I) ≠ ⟨0⟩)
    (hsel : (bytesStoreLiteLowTakenSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc i))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize
    bytesStoreLiteSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteRootLowJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreLiteSplitWellFormed
        hfirst (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowSplitPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLiteLowSplitPc, bytesStoreLiteRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have htakenJd : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowTakenJumpdestPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hlowSplit bytesStoreLiteLowSplitWellFormed
        hsecond (by native_decide) (by native_decide)
    simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitTgt] using hstep
  obtain ⟨kT, CT, htakenJdRD⟩ := htakenJd
  have hfirstArm : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLiteLowTakenFirstArmPc [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kT + 1, CT + 1, ?_⟩
    simpa [bytesStoreLiteLowTakenFirstArmPc, bytesStoreLiteLowTakenJumpdestPc] using
      htakenJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreLiteLowTakenMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLiteLowTakenArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreLiteSelectorPivot_eq0 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (sel : ByteArray) (c0 c1 c2 c3 : UInt8) (word : UInt256)
    (hsel : selIs I sel)
    (hselLit : sel = ⟨#[c0, c1, c2, c3]⟩)
    (hword : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = word.toNat)
    (pc : UInt256)
    (h : UInt256.gt (armSelNat bytesStoreLiteBytecode pc) word = ⟨0⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode pc) (bytesStoreLiteSelWord I) = ⟨0⟩ := by
  have hw : bytesStoreLiteSelWord I = word := by
    subst hselLit
    exact bytesStoreLiteSelWord_eq_of_beq I hsz c0 c1 c2 c3 word hword
      (by simpa [selIs] using hsel)
  simpa [hw] using h

theorem bytesStoreLiteSelectorPivot_ne0 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (sel : ByteArray) (c0 c1 c2 c3 : UInt8) (word : UInt256)
    (hsel : selIs I sel)
    (hselLit : sel = ⟨#[c0, c1, c2, c3]⟩)
    (hword : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = word.toNat)
    (pc : UInt256)
    (h : UInt256.gt (armSelNat bytesStoreLiteBytecode pc) word ≠ ⟨0⟩) :
    UInt256.gt (armSelNat bytesStoreLiteBytecode pc) (bytesStoreLiteSelWord I) ≠ ⟨0⟩ := by
  have hw : bytesStoreLiteSelWord I = word := by
    subst hselLit
    exact bytesStoreLiteSelWord_eq_of_beq I hsz c0 c1 c2 c3 word hword
      (by simpa [selIs] using hsel)
  simpa [hw] using h

theorem bytesStoreLiteReachSetByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 1))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachLowFallthroughArm 1 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x1c 0x52 0x47 0x7d ⟨0x1c52477d⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0x1c 0x52 0x47 0x7d ⟨0x1c52477d⟩
      hsel rfl (by native_decide) bytesStoreLiteLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteLowFallthroughSelBytes] using hsel)

theorem bytesStoreLiteReachSetChunk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 3))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachLowFallthroughArm 3 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x39 0x3d 0x9c 0xd7 ⟨0x393d9cd7⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0x39 0x3d 0x9c 0xd7 ⟨0x393d9cd7⟩
      hsel rfl (by native_decide) bytesStoreLiteLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteLowFallthroughSelBytes] using hsel)

theorem bytesStoreLiteReachSetChunkByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc 0))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachMidLowArm 0 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0x48 0x1c 0x2f 0xfb ⟨0x481c2ffb⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x48 0x1c 0x2f 0xfb ⟨0x481c2ffb⟩
      hsel rfl (by native_decide) bytesStoreLiteHighSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteMidLowSelBytes] using hsel)

theorem bytesStoreLiteReachSetPacket {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 0))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachLowFallthroughArm 0 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x14 0xf1 0x7c 0x69 ⟨0x14f17c69⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0x14 0xf1 0x7c 0x69 ⟨0x14f17c69⟩
      hsel rfl (by native_decide) bytesStoreLiteLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteLowFallthroughSelBytes] using hsel)

theorem bytesStoreLiteReachSetPacketByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 1))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachLowTakenArm 1 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x0a 0xb2 0x59 0x00 ⟨0x0ab25900⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x0a 0xb2 0x59 0x00 ⟨0x0ab25900⟩
      hsel rfl (by native_decide) bytesStoreLiteLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteLowTakenSelBytes] using hsel)

theorem bytesStoreLiteReachSetMapped {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc 2))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachHighArm 2 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0xe1 0x91 0x9b 0x17 ⟨0xe1919b17⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_eq0 hsz _ 0xe1 0x91 0x9b 0x17 ⟨0xe1919b17⟩
      hsel rfl (by native_decide) bytesStoreLiteHighSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteHighSelBytes] using hsel)

theorem bytesStoreLiteReachSetMappedByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 2))
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreLiteReachLowTakenArm 2 (by decide)
    hcode hwv hsz hsize
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x13 0x2f 0xa3 0x46 ⟨0x132fa346⟩
      hsel rfl (by native_decide) bytesStoreLiteSplitPc (by native_decide))
    (bytesStoreLiteSelectorPivot_ne0 hsz _ 0x13 0x2f 0xa3 0x46 ⟨0x132fa346⟩
      hsel rfl (by native_decide) bytesStoreLiteLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLiteLowTakenSelBytes] using hsel)

theorem bytesStoreLiteSetEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 0) = ⟨244⟩ := by
  native_decide

theorem bytesStoreLiteSetByteEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 1) = ⟨357⟩ := by
  native_decide

theorem bytesStoreLiteSetChunkEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 3) = ⟨395⟩ := by
  native_decide

theorem bytesStoreLiteSetChunkByteEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc 0) = ⟨414⟩ := by
  native_decide

theorem bytesStoreLiteSetPacketEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 0) = ⟨338⟩ := by
  native_decide

theorem bytesStoreLiteSetPacketByteEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 1) = ⟨282⟩ := by
  native_decide

theorem bytesStoreLiteSetMappedEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc 2) = ⟨484⟩ := by
  native_decide

theorem bytesStoreLiteSetMappedByteEntryPc :
    armTgt bytesStoreLiteBytecode
      (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 2) = ⟨319⟩ := by
  native_decide

theorem bytesStoreLiteReachSetEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨244⟩
        [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  simpa [bytesStoreLiteSetEntryPc] using
    (bytesStoreLiteReachSet (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel)

theorem bytesStoreLiteReachSetDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1883⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨258⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreLiteReachSetEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨258⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨1883⟩, jump (by native_decide)])⟩

/-! ## No-dispatch short calldata -/

theorem bytesStoreLiteX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt bytesStoreLiteBytecode)
    (opC := solcGuardTgtOp bytesStoreLiteBytecode)
    (wC := solcGuardTgtWidth bytesStoreLiteBytecode)
    (solcGuardPrologueRD hcode (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide))
    hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreLiteBodyReverts_nonPayable
    (t : TransitionDecl) (ht : t ∈ bytesStoreLiteContract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm locals t.body .reverted := by
  rw [bytesStoreLiteTransitions] at ht
  simp at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  all_goals subst t
  all_goals exact bodyReverts_nonPayable h

theorem bytesStoreLiteNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (bytesStoreLiteX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg bytesStoreLiteContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ bytesStoreLiteContract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (bytesStoreLiteBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem bytesStoreLiteX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt bytesStoreLiteBytecode)
    (opC := solcGuardTgtOp bytesStoreLiteBytecode)
    (wC := solcGuardTgtWidth bytesStoreLiteBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc bytesStoreLiteBytecode)
    (rtgt := solcCalldataRevertTgt bytesStoreLiteBytecode)
    (opR := solcCalldataRevertTgtOp bytesStoreLiteBytecode)
    (wR := solcCalldataRevertTgtWidth bytesStoreLiteBytecode)
    h1 hsz (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreLiteShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hshort : I.calldata.size < 4) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact (bytesStoreLiteX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch
      hcode (bytesStoreLiteDispatch_none_short hshort)
  · exact bytesStoreLiteNonPayable hcode hwv

theorem bytesStoreLiteX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 15 → (bytesStoreLiteSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLiteHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteHighSelBytes, bytesStoreLiteSelBytes] using hnm 4 (by omega)
      rw [bytesStoreLiteHighArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteHighSelBytes, bytesStoreLiteSelBytes] using hnm 10 (by omega)
      rw [bytesStoreLiteHighArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteHighSelBytes, bytesStoreLiteSelBytes] using hnm 12 (by omega)
      rw [bytesStoreLiteHighArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteHighSelBytes, bytesStoreLiteSelBytes] using hnm 7 (by omega)
      rw [bytesStoreLiteHighArmEq I hsz 3 (by omega), hm]
      rfl
  have heqMidLow0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLiteMidLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteMidLowSelBytes, bytesStoreLiteSelBytes] using hnm 6 (by omega)
      rw [bytesStoreLiteMidLowArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteMidLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteMidLowSelBytes, bytesStoreLiteSelBytes] using hnm 11 (by omega)
      rw [bytesStoreLiteMidLowArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteMidLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteMidLowSelBytes, bytesStoreLiteSelBytes] using hnm 3 (by omega)
      rw [bytesStoreLiteMidLowArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteMidLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteMidLowSelBytes, bytesStoreLiteSelBytes] using hnm 2 (by omega)
      rw [bytesStoreLiteMidLowArmEq I hsz 3 (by omega), hm]
      rfl
  have heqLowFallthrough0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLiteLowFallthroughSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowFallthroughSelBytes, bytesStoreLiteSelBytes] using hnm 8 (by omega)
      rw [bytesStoreLiteLowFallthroughArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteLowFallthroughSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowFallthroughSelBytes, bytesStoreLiteSelBytes] using hnm 1 (by omega)
      rw [bytesStoreLiteLowFallthroughArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteLowFallthroughSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowFallthroughSelBytes, bytesStoreLiteSelBytes] using hnm 14 (by omega)
      rw [bytesStoreLiteLowFallthroughArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteLowFallthroughSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowFallthroughSelBytes, bytesStoreLiteSelBytes] using hnm 5 (by omega)
      rw [bytesStoreLiteLowFallthroughArmEq I hsz 3 (by omega), hm]
      rfl
  have heqLowTaken0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat bytesStoreLiteBytecode
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc j))
        (bytesStoreLiteSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLiteLowTakenSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowTakenSelBytes, bytesStoreLiteSelBytes] using hnm 0 (by omega)
      rw [bytesStoreLiteLowTakenArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteLowTakenSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowTakenSelBytes, bytesStoreLiteSelBytes] using hnm 9 (by omega)
      rw [bytesStoreLiteLowTakenArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLiteLowTakenSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteLowTakenSelBytes, bytesStoreLiteSelBytes] using hnm 13 (by omega)
      rw [bytesStoreLiteLowTakenArmEq I hsz 2 (by omega), hm]
      rfl
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteBytecode) (firstPc := bytesStoreLiteSplitPc)
    hcode hwv hsz hsize bytesStoreLiteSolcDispatchPrefix (by native_decide)
  by_cases hpivot0 : UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteSplitPc)
      (bytesStoreLiteSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit bytesStoreLiteSplitWellFormed hpivot0
      (by native_decide)
    have h41' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreLiteHighSplitPc [bytesStoreLiteSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5, CS + 22, ?_⟩
      simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitNextPc] using h41
    obtain ⟨kH, CH, hhigh⟩ := h41'
    by_cases hpivot1 : UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteHighSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩
    · have h52 := RD.selectorSplitNotTakenAuto hhigh bytesStoreLiteHighSplitWellFormed hpivot1
        (by native_decide)
      have h52' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteHighFirstArmPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kH + 5, CH + 22, ?_⟩
        simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitNextPc] using h52
      obtain ⟨k52, C52, h52rd⟩ := h52'
      have h96 := h52rd
        |>.selectorArmNotTakenAuto (bytesStoreLiteHighArmsWellFormed 0 (by omega))
            (heqHigh0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteHighArmsWellFormed 1 (by omega))
            (heqHigh0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteHighArmsWellFormed 2 (by omega))
            (heqHigh0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteHighArmsWellFormed 3 (by omega))
            (heqHigh0 3 (by omega)) (by native_decide)
      have h96rd : RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨96⟩ [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k52 + 5 + 5 + 5 + 5) (C52 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteHighFirstArmPc 4)
          [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k52 + 5 + 5 + 5 + 5) (C52 + 22 + 22 + 22 + 22) at h96
        simpa [bytesStoreLiteHighArmsEnd] using h96
      exact h96rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have h99 := RD.selectorSplitTakenAuto hhigh bytesStoreLiteHighSplitWellFormed hpivot1
        (by native_decide) (by native_decide)
      have h99' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteMidLowJumpdestPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kH + 5, CH + 22, ?_⟩
        simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteHighSplitTgt] using h99
      obtain ⟨kJ, CJ, h99rd⟩ := h99'
      have h100 : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteMidLowFirstArmPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kJ + 1, CJ + 1, ?_⟩
        simpa [bytesStoreLiteMidLowFirstArmPc, bytesStoreLiteMidLowJumpdestPc] using
          h99rd.jumpdest (by native_decide) (by simp)
      obtain ⟨k100, C100, h100rd⟩ := h100
      have h144 := h100rd
        |>.selectorArmNotTakenAuto (bytesStoreLiteMidLowArmsWellFormed 0 (by omega))
            (heqMidLow0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteMidLowArmsWellFormed 1 (by omega))
            (heqMidLow0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteMidLowArmsWellFormed 2 (by omega))
            (heqMidLow0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteMidLowArmsWellFormed 3 (by omega))
            (heqMidLow0 3 (by omega)) (by native_decide)
      have h144rd : RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨144⟩ [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k100 + 5 + 5 + 5 + 5) (C100 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteMidLowFirstArmPc 4)
          [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k100 + 5 + 5 + 5 + 5) (C100 + 22 + 22 + 22 + 22) at h144
        simpa [bytesStoreLiteMidLowArmsEnd] using h144
      exact h144rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · have h147 := RD.selectorSplitTakenAuto hsplit bytesStoreLiteSplitWellFormed hpivot0
      (by native_decide) (by native_decide)
    have h147' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreLiteRootLowJumpdestPc [bytesStoreLiteSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5, CS + 22, ?_⟩
      simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteSplitTgt] using h147
    obtain ⟨kJ, CJ, h147rd⟩ := h147'
    have h148 : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreLiteLowSplitPc [bytesStoreLiteSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kJ + 1, CJ + 1, ?_⟩
      simpa [bytesStoreLiteLowSplitPc, bytesStoreLiteRootLowJumpdestPc] using
        h147rd.jumpdest (by native_decide) (by simp)
    obtain ⟨kL, CL, hlow⟩ := h148
    by_cases hpivotL : UInt256.gt (armSelNat bytesStoreLiteBytecode bytesStoreLiteLowSplitPc)
        (bytesStoreLiteSelWord I) = ⟨0⟩
    · have h159 := RD.selectorSplitNotTakenAuto hlow bytesStoreLiteLowSplitWellFormed hpivotL
        (by native_decide)
      have h159' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteLowFallthroughFirstArmPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kL + 5, CL + 22, ?_⟩
        simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitNextPc] using h159
      obtain ⟨k159, C159, h159rd⟩ := h159'
      have h203 := h159rd
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowFallthroughArmsWellFormed 0 (by omega))
            (heqLowFallthrough0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowFallthroughArmsWellFormed 1 (by omega))
            (heqLowFallthrough0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowFallthroughArmsWellFormed 2 (by omega))
            (heqLowFallthrough0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowFallthroughArmsWellFormed 3 (by omega))
            (heqLowFallthrough0 3 (by omega)) (by native_decide)
      have h203rd : RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨203⟩ [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k159 + 5 + 5 + 5 + 5) (C159 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowFallthroughFirstArmPc 4)
          [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k159 + 5 + 5 + 5 + 5) (C159 + 22 + 22 + 22 + 22) at h203
        simpa [bytesStoreLiteLowFallthroughArmsEnd] using h203
      exact h203rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have h206 := RD.selectorSplitTakenAuto hlow bytesStoreLiteLowSplitWellFormed hpivotL
        (by native_decide) (by native_decide)
      have h206' : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteLowTakenJumpdestPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kL + 5, CL + 22, ?_⟩
        simpa [bytesStoreLiteSelWord, solcSelectorWord, bytesStoreLiteLowSplitTgt] using h206
      obtain ⟨kJ2, CJ2, h206rd⟩ := h206'
      have h207 : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLiteLowTakenFirstArmPc [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kJ2 + 1, CJ2 + 1, ?_⟩
        simpa [bytesStoreLiteLowTakenFirstArmPc, bytesStoreLiteLowTakenJumpdestPc] using
          h206rd.jumpdest (by native_decide) (by simp)
      obtain ⟨k207, C207, h207rd⟩ := h207
      have h240 := h207rd
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowTakenArmsWellFormed 0 (by omega))
            (heqLowTaken0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowTakenArmsWellFormed 1 (by omega))
            (heqLowTaken0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLiteLowTakenArmsWellFormed 2 (by omega))
            (heqLowTaken0 2 (by omega)) (by native_decide)
      have h240rd : RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨240⟩ [bytesStoreLiteSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k207 + 5 + 5 + 5) (C207 + 22 + 22 + 22) := by
        change RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreLiteBytecode bytesStoreLiteLowTakenFirstArmPc 3)
          [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k207 + 5 + 5 + 5) (C207 + 22 + 22 + 22) at h240
        simpa [bytesStoreLiteLowTakenArmsEnd] using h240
      have h241 := h240rd.jumpdest (by native_decide) (by simp)
      exact h241.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 15 → (bytesStoreLiteSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases hwv : I.weiValue = ⟨0⟩
    · exact (bytesStoreLiteX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
        |>.reEquivNoDispatch hcode (bytesStoreLiteDispatch_none_nomatch hnm)
    · exact (bytesStoreLiteX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv)
        |>.reEquivNoDispatch hcode (bytesStoreLiteDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact bytesStoreLiteShortRevert hcode hshort

/-! ## EVM and Solm body facts -/

def packetTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

theorem packetTagWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    packetTagWord σ_evm I = packetTagWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩

def bytesStoreLiteSetByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreLiteSetByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreLiteFullPanicSelectorWord : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def bytesStoreLiteFullPanic22Mem1 : ByteArray :=
  bytesStoreLiteFullPanicSelectorWord.toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def bytesStoreLiteFullPanic22Mem : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 bytesStoreLiteFullPanic22Mem1 4 32

noncomputable def bytesStoreLiteFullPanic22Mem1From (mem : ByteArray) : ByteArray :=
  bytesStoreLiteFullPanicSelectorWord.toByteArray.write 0 mem 0 32

noncomputable def bytesStoreLiteFullPanic22MemFrom (mem : ByteArray) : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 (bytesStoreLiteFullPanic22Mem1From mem) 4 32

noncomputable def bytesStoreLiteFullPanicMemFrom (code : UInt256) (mem : ByteArray) : ByteArray :=
  code.toByteArray.write 0 (bytesStoreLiteFullPanic22Mem1From mem) 4 32

noncomputable abbrev currentLengthZeroAllocMem : ByteArray :=
  BytesStoreLiteCore.currentLengthZeroAllocMem

noncomputable abbrev currentLengthZeroMem : ByteArray :=
  BytesStoreLiteCore.currentLengthZeroMem

noncomputable abbrev currentLengthZeroReturnMem : ByteArray :=
  BytesStoreLiteCore.currentLengthZeroReturnMem

def currentLengthAllocSize (len : UInt256) : UInt256 :=
  BytesStoreLiteCore.currentLengthAllocSize len

def currentLengthFreePtr (len : UInt256) : UInt256 :=
  BytesStoreLiteCore.currentLengthFreePtr len

noncomputable abbrev currentLengthAllocMem (len : UInt256) : ByteArray :=
  BytesStoreLiteCore.currentLengthAllocMem len

noncomputable abbrev currentLengthMem (len : UInt256) : ByteArray :=
  BytesStoreLiteCore.currentLengthMem len

def currentLengthPayloadWord (header : UInt256) : UInt256 :=
  BytesStoreLiteCore.currentLengthPayloadWord header

noncomputable abbrev currentLengthPayloadMem (len header : UInt256) : ByteArray :=
  BytesStoreLiteCore.currentLengthPayloadMem len header

noncomputable abbrev currentLengthPayloadReturnMem (len header : UInt256) : ByteArray :=
  BytesStoreLiteCore.currentLengthPayloadReturnMem len header

theorem currentLengthZeroMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact BytesStoreLiteCore.currentLengthZeroMem_mload128

theorem currentLengthZeroMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact BytesStoreLiteCore.currentLengthZeroMem_mload64

theorem currentLengthZeroReturnMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact BytesStoreLiteCore.currentLengthZeroReturnMem_mload64

theorem currentLengthZeroReturnMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact BytesStoreLiteCore.currentLengthZeroReturnMem_mload128

theorem currentLengthZeroReturnMem_read160 :
    currentLengthZeroReturnMem.readWithPadding 160 32 = UInt256.toByteArray ⟨0⟩ := by
  exact BytesStoreLiteCore.currentLengthZeroReturnMem_read160

theorem currentLengthPayloadMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
  exact BytesStoreLiteCore.currentLengthPayloadMem_mload64 len header freePtr hfree

theorem currentLengthPayloadMem_mload128 (len header : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        len := by
  exact BytesStoreLiteCore.currentLengthPayloadMem_mload128 len header

theorem currentLengthPayloadReturnMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadReturnMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadReturnMem len header).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact BytesStoreLiteCore.currentLengthPayloadReturnMem_mload64 len header freePtr hfree

theorem currentLengthPayloadReturnMem_read192 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  exact BytesStoreLiteCore.currentLengthPayloadReturnMem_read192 len header

theorem currentLength_short_valid_lt32 {len : UInt256}
    (hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len.toNat < 32 :=
  BytesStoreLiteCore.currentLength_short_valid_lt32 hvalid0

theorem currentLength_notGt31_of_lt32 {len : UInt256} (hlt32 : len.toNat < 32) :
    UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
  BytesStoreLiteCore.currentLength_notGt31_of_lt32 hlt32

theorem bytesStoreLite_shiftLeft_one_eq_mul_two_of_short {len : UInt256}
    (_hshort : len.toNat < 32) :
    UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
  show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
  rw [Nat.shiftLeft_eq]

theorem bytesStoreLite_shiftLeft_three_eq_mul_eight_of_short {len : UInt256}
    (_hshort : len.toNat < 32) :
    UInt256.shiftLeft len ⟨3⟩ = UInt256.mul len ⟨8⟩ := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨3⟩ : UInt256).val ≥ 256)]
  show (len.toNat <<< 3) % UInt256.size = (len.toNat * 8) % UInt256.size
  rw [Nat.shiftLeft_eq]

theorem bytesStoreLite_nat_land_248_shiftLeft_three_mod_size (n : Nat) :
    Nat.land 248 ((n <<< 3) % UInt256.size) = 8 * (n % 32) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((248 : Nat) &&& ((n <<< 3) % UInt256.size)).testBit i =
    (8 * (n % 32)).testBit i
  rw [Nat.testBit_and]
  have hrhs : 8 * (n % 32) = (n % 32) <<< 3 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    rw [Nat.mul_comm]
  rw [hrhs]
  rw [nat_testBit_shiftLeft]
  rw [show UInt256.size = 2 ^ 256 from rfl, Nat.testBit_mod_two_pow]
  rw [nat_testBit_shiftLeft]
  by_cases hi3 : i < 3
  · have h248 : (248 : Nat).testBit i = false := by
      interval_cases i <;> native_decide
    simp [hi3, h248]
  · have hge3 : 3 ≤ i := Nat.le_of_not_gt hi3
    by_cases hi8 : i < 8
    · have hi256 : i < 256 := by omega
      have him3lt5 : i - 3 < 5 := by omega
      have h248 : (248 : Nat).testBit i = true := by
        interval_cases i <;> native_decide
      rw [show 32 = 2 ^ 5 by norm_num, Nat.testBit_mod_two_pow]
      simp [hi3, hi256, h248, him3lt5]
    · have hge8 : 8 ≤ i := Nat.le_of_not_gt hi8
      have h248 : (248 : Nat).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have hpow : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge8
        exact lt_of_lt_of_le (by norm_num) hpow
      have hmodBit : (n % 32).testBit (i - 3) = false := by
        apply Nat.testBit_lt_two_pow
        have hmod : n % 32 < 32 := Nat.mod_lt _ (by decide : 0 < 32)
        have hpow : 32 ≤ 2 ^ (i - 3) := by
          change 2 ^ 5 ≤ 2 ^ (i - 3)
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact lt_of_lt_of_le hmod hpow
      simp [hi3, h248, hmodBit]

theorem bytesStoreLite_optimizedLongTailMaskShift_eq_core (len : UInt256) :
    UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩) =
      UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩) := by
  apply u256_inj
  rw [u256_land_toNat, u256_mul_toNat, BytesStoreLiteCore.u256_land_31_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨3⟩ : UInt256).val ≥ 256)]
  change Nat.land 248 ((len.toNat <<< 3) % UInt256.size) % UInt256.size =
    (8 * (len.toNat % 32)) % UInt256.size
  rw [bytesStoreLite_nat_land_248_shiftLeft_three_mod_size]

theorem bytesStoreLiteOptimizedLongTailMaskedWord_eq_core (word len : UInt256) :
    UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
          (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))))
      word =
      BytesStoreLiteCore.longDataTailMaskedWord word len := by
  rw [bytesStoreLite_optimizedLongTailMaskShift_eq_core]
  unfold BytesStoreLiteCore.longDataTailMaskedWord
  rw [u256_land_comm]

theorem bytesStoreLiteOptimizedShortStoredWord_eq_setShortPackedHeader
    (payloadWord len : UInt256) (hshort : len.toNat < 32) :
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord) =
      BytesStoreLiteCore.setShortPackedHeader payloadWord len := by
  rw [BytesStoreLiteCore.setShortPackedHeader]
  rw [bytesStoreLite_shiftLeft_one_eq_mul_two_of_short hshort]
  rw [bytesStoreLite_shiftLeft_three_eq_mul_eight_of_short hshort]
  rw [u256_mul_comm len ⟨2⟩]
  rw [u256_mul_comm len ⟨8⟩]
  rw [u256_land_comm
    (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len)))
    payloadWord]
  rw [u256_lor_comm]

theorem bytesStoreLiteShortDecodedPayloadReadWithPadding_toList {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding 0 32).toList =
      (I.calldata.toList.drop payloadStart.toNat).take len.toNat ++
        List.replicate (32 - len.toNat) 0 := by
  rw [BytesStoreLiteCore.setDecodedValueBytes_readWithPadding_short_toList
    (I := I)
    (by simpa [← hlenAbi] using hshort)
    (by simpa [← hlenAbi] using hnz)
    hpayload]
  rw [BytesStoreLiteCore.setDecodedValueBytes_eq_extract hlenAbi hpayloadStart hoffMax]
  rw [byteArray_toList_eq (I.calldata.extract payloadStart.toNat
    (payloadStart.toNat + len.toNat))]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq I.calldata]
  rw [show payloadStart.toNat + len.toNat - payloadStart.toNat = len.toNat by omega]
  rw [show (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat =
      len.toNat by rw [hlenAbi]]

theorem bytesStoreLiteShortPayloadMaskedCallDataWord_eq_decodedWord {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    UInt256.land
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32))
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len))) =
      uInt256OfByteArray
        ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding 0 32) := by
  rw [BytesStoreLiteCore.setShortPackedHeader_mask_of_short hshort]
  rw [uInt256OfByteArray_readBytes_at_high_mask_eq_padded
    I.calldata payloadStart.toNat len.toNat hshort hsrc]
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq]
  rw [← byteArray_toList_eq
    ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding 0 32)]
  rw [bytesStoreLiteShortDecodedPayloadReadWithPadding_toList
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hpayload]
  rw [byteArray_toList_eq]

theorem bytesStoreLiteOptimizedShortStoredWord_eq_solidityShortBytesWord {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32))) =
      solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I) := by
  rw [bytesStoreLiteOptimizedShortStoredWord_eq_setShortPackedHeader
    (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)) len hshort]
  have hpayloadWord :=
    bytesStoreLiteShortPayloadMaskedCallDataWord_eq_decodedWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload
  have hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat := by
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload]
    rw [hlenAbi]
  have htag :
      UInt256.mul ⟨2⟩ len =
        UInt256.ofNat ((BytesStoreLiteCore.setDecodedValueBytes I).size * 2) := by
    apply u256_inj
    rw [u256_mul_toNat]
    change (2 * len.toNat) % UInt256.size =
      ((BytesStoreLiteCore.setDecodedValueBytes I).size * 2) % UInt256.size
    rw [hsize, Nat.mul_comm]
  rw [BytesStoreLiteCore.setShortPackedHeader,
    solidityShortBytesWord]
  rw [hpayloadWord]
  rw [htag]

abbrev bytesStoreLiteOptimizedShortStoredWord
    (I : ExecutionEnv) (len payloadStart : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
    (UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
      (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))

theorem bytesStoreLiteOptimizedShortStoredWord_abbrev_eq_solidityShortBytesWord
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    bytesStoreLiteOptimizedShortStoredWord I len payloadStart =
      solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I) := by
  exact bytesStoreLiteOptimizedShortStoredWord_eq_solidityShortBytesWord
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload

theorem bytesStoreLiteSetHelperShortStoredWord_eq_solidityShortBytesWord
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart)) =
      solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I) := by
  rw [bytesStoreLiteOptimizedShortStoredWord_eq_setShortPackedHeader
    (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart) len hshort]
  exact BytesStoreLiteCore.setShortPackedHeader_eq_solidityShortBytesWord
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload

theorem bytesStoreLiteSetDecodedShortReturnEquiv {I : ExecutionEnv} {len : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    returnEquiv (UInt256.toByteArray len)
      (some (.int (BytesStoreLiteCore.setDecodedValueBytes I).size))
      setTransition.returnType := by
  have hlenSize : len.toNat = (BytesStoreLiteCore.setDecodedValueBytes I).size := by
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload, hlenAbi]
  change returnEquiv (UInt256.toByteArray len)
    (some (.int (BytesStoreLiteCore.setDecodedValueBytes I).size))
    (some (.elem (.int (.uint ⟨256, by decide⟩))))
  rw [← hlenSize]
  exact returnEquiv_of_encode (uint256ReturnEncoding len)

theorem currentLengthFreePtr_eq_192_of_short_nonzero {len : UInt256}
    (hnonzero : len ≠ ⟨0⟩) (hlt32 : len.toNat < 32) :
    currentLengthFreePtr len = ⟨192⟩ :=
  BytesStoreLiteCore.currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32

theorem bytesStoreLiteStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [uint256Loc] using storageLocLoad_uint256 evm slot

theorem bytesStoreLiteCurrentLengthResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
  have hbase :
      (∅ : Store).get? currentRef.base = none := by
    simp [currentRef]
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := ∅ } evm currentRef =
          .ok ({ base := "current", steps := [] } : EvaledStorageRef) := by
    simpa [currentRef] using
      (evalStorageRef_base
        (cfg := bytesStoreLiteConfig)
        (solm := { contract := bytesStoreLiteContract, locals := ∅ })
        (evm := evm) (base := "current"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])

theorem bytesStoreLiteCurrentResolveOfGetNone {evm : EVM.State} {locals : Store}
    (hbase : locals.get? currentRef.base = none) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := locals } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := locals } evm currentRef =
          .ok ({ base := "current", steps := [] } : EvaledStorageRef) := by
    simpa [currentRef] using
      (evalStorageRef_base
        (cfg := bytesStoreLiteConfig)
        (evm := evm) (base := "current"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])

theorem bytesStoreLiteChunksResolve (evm : EVM.State) :
    resolveDynamicArrayRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .bytes) := by
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
    have hbase :
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)).get? chunksRef.base = none := by
      simp [chunksRef, Std.HashMap.get?_eq_getElem?]
    have her :
        evalStorageRef bytesStoreLiteConfig
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evm chunksRef =
            .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
      simpa [chunksRef] using
        (evalStorageRef_base
          (cfg := bytesStoreLiteConfig)
          (evm := evm) (base := "chunks"))
    exact resolveStorageRef?_ok hbase her (by
      simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])
  exact resolveDynamicArrayRef?_ok_of_resolve hresolve

theorem bytesStoreLiteChunksResolveValue (evm : EVM.State) (value : ByteArray) :
    resolveDynamicArrayRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .bytes) := by
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
    have hbase :
        ((∅ : Store).insert "value" (.bytes value)).get? chunksRef.base = none := by
      simp [chunksRef, Std.HashMap.get?_eq_getElem?]
    have her :
        evalStorageRef bytesStoreLiteConfig
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evm chunksRef =
            .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
      simpa [chunksRef] using
        (evalStorageRef_base
          (cfg := bytesStoreLiteConfig)
          (evm := evm) (base := "chunks"))
    exact resolveStorageRef?_ok hbase her (by
      simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])
  exact resolveDynamicArrayRef?_ok_of_resolve hresolve

theorem bytesStoreLiteChunksStorageResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
  have hbase :
      ((∅ : Store).insert "value" (.bytes ByteArray.empty)).get? chunksRef.base = none := by
    simp [chunksRef, Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
    simpa [chunksRef] using
      (evalStorageRef_base
        (cfg := bytesStoreLiteConfig)
        (evm := evm) (base := "chunks"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])

theorem bytesStoreLiteChunksStorageResolveValue (evm : EVM.State) (value : ByteArray) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
  have hbase :
      ((∅ : Store).insert "value" (.bytes value)).get? chunksRef.base = none := by
    simp [chunksRef, Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
    simpa [chunksRef] using
      (evalStorageRef_base
        (cfg := bytesStoreLiteConfig)
        (evm := evm) (base := "chunks"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, bytesSt])

theorem bytesStoreLiteChunksArrayLengthEval (evm : EVM.State) :
    evalExpr? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm (.arrayLength .storage chunksRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  rw [evalExpr?, bytesStoreLiteChunksStorageResolve evm]
  simp only [readStorageArrayLength?, bytesStoreLiteConfig, bytesStoreLiteStorageLayout,
    solidityStorageLayout, bytesStoreLiteLayout, EvalResult.bind, bind, pure, List.nil_append]
  rw [bytesStoreLiteStorageLocLoad_uint256]

theorem bytesStoreLiteChunksArrayLengthEvalValue (evm : EVM.State) (value : ByteArray) :
    evalExpr? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm (.arrayLength .storage chunksRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  rw [evalExpr?, bytesStoreLiteChunksStorageResolveValue evm value]
  simp only [readStorageArrayLength?, bytesStoreLiteConfig, bytesStoreLiteStorageLayout,
    solidityStorageLayout, bytesStoreLiteLayout, EvalResult.bind, bind, pure, List.nil_append]
  rw [bytesStoreLiteStorageLocLoad_uint256]

theorem bytesStoreLiteCurrentLengthBaseSlot {evm : EVM.State} :
    ∃ loc, bytesStoreLiteLayout { base := "current", steps := [.length] } evm =
      some loc ∧ loc.slot = ⟨0⟩ := by
  refine ⟨bytesLikeLengthLoc ⟨0⟩ evm, ?_, by simp⟩
  simp [bytesStoreLiteLayout]

theorem bytesStoreLiteChunksLengthBaseSlot {evm : EVM.State} :
    ∃ loc, bytesStoreLiteLayout { base := "chunks", steps := [.length] } evm =
      some loc ∧ loc.slot = ⟨1⟩ := by
  refine ⟨uint256Loc ⟨1⟩, ?_, by simp [uint256Loc]⟩
  simp [bytesStoreLiteLayout]

theorem bytesStoreLiteChunkElemLengthBaseSlot {evm : EVM.State} (oldLen : UInt256) :
    ∃ loc,
      bytesStoreLiteLayout
          { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat)), .length] }
          evm =
        some loc ∧ loc.slot = chunksDataBase + oldLen := by
  have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
    not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
  refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
  simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
    hnonneg, u256_ofNat_toNat oldLen]

theorem bytesStoreLiteWriteEmptyChunkAt {evm : EVM.State} (oldLen : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) ⟨0⟩) := by
  exact writeSolidityBytesEmptyFromZero
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload

theorem bytesStoreLiteWriteEmptyChunkShortPacked {evm : EVM.State}
    (oldLen header len : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) ⟨0⟩) := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := ByteArray.empty)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    (by decide) hload hpacked hflag hlen hvalid
  simpa [hshortEmpty] using hwrite

theorem bytesStoreLiteWriteChunkShortPacked {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWriteChunkLongPacked {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreLiteChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWriteChunkLongPackedAbsent {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .ok evm := by
  exact writeSolidityBytesLongPackedAbsent
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreLiteChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hpacked hflag hlen hvalid hmissing

theorem bytesStoreLiteWriteChunkLongFromLongPrepared {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreLiteChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWriteChunkShortFromLongPrepared {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) 0
          ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) 0
          ((len.toNat + 31) / 32)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreLiteChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWriteChunkMalformedLong {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload hflag hbad

theorem bytesStoreLiteWriteChunkMalformedShort {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload hflag hbad

theorem bytesStoreLiteWordOfIntOfNatEq (n : Nat) :
    EVM.wordOfInt (Int.ofNat n) = UInt256.ofNat n := by
  exact wordOfInt_ofNat_eq n

theorem bytesStoreLiteStorageLocStore_uint256_nat
    (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat n)) := by
  exact storageLocStore_uint256_nat evm slot n

theorem bytesStoreLiteStorageLocStore_uint256_addOne
    (evm : EVM.State) (slot oldLen : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat oldLen.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (oldLen + ⟨1⟩)) := by
  have hword : UInt256.ofNat (oldLen.toNat + 1) = oldLen + (⟨1⟩ : UInt256) := by
    apply u256_inj
    show (oldLen.toNat + 1) % UInt256.size =
      (oldLen + (⟨1⟩ : UInt256)).toNat
    rw [uadd_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
  simpa [Nat.cast_add, hword] using
    bytesStoreLiteStorageLocStore_uint256_nat evm slot (oldLen.toNat + 1)

theorem bytesStoreLitePushChunkEmptyPushArray_of_post_header {evm : EVM.State} (oldLen : UInt256)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract,
      locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes ByteArray.empty) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) ⟨0⟩) := by
    exact bytesStoreLiteWriteEmptyChunkAt (evm := evmLen) oldLen
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
  rw [pushArray?, bytesStoreLiteChunksResolve evm]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreLiteConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) ⟨0⟩)
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStoreLitePushChunkEmptyPushArray_of_ne {evm : EVM.State} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  exact bytesStoreLitePushChunkEmptyPushArray_of_post_header (evm := evm) oldLen hloadLen
    (bytesStoreLiteEmptyChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen hne hloadElem)

theorem bytesStoreLitePushChunkMalformedLongPushArray_of_post_header {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) = .revert := by
    exact bytesStoreLiteWriteChunkMalformedLong (evm := evmLen)
      oldLen header value
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hbad
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  exact hwrite

theorem bytesStoreLitePushChunkMalformedLongPushArray_of_ne {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  exact bytesStoreLitePushChunkMalformedLongPushArray_of_post_header (evm := evm)
    oldLen header value hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hbad

theorem bytesStoreLitePushChunkMalformedShortPushArray_of_post_header {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) = .revert := by
    exact bytesStoreLiteWriteChunkMalformedShort (evm := evmLen)
      oldLen header value
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hbad
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  exact hwrite

theorem bytesStoreLitePushChunkMalformedShortPushArray_of_ne {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  exact bytesStoreLitePushChunkMalformedShortPushArray_of_post_header (evm := evm)
    oldLen header value hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hbad

theorem bytesStoreLitePushChunkEmptyPushArrayShortPacked_of_post_header {evm : EVM.State}
    (oldLen header len : UInt256)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract,
      locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hpackedLen : checkBytesPacked (chunksDataBase + oldLen) evmLen = true :=
    checkBytesPacked_of_storageLoad_land_one_zero
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes ByteArray.empty) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) ⟨0⟩) := by
    exact bytesStoreLiteWriteEmptyChunkShortPacked (evm := evmLen)
      oldLen header len
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
      hpackedLen hflag hlen hvalid
  rw [pushArray?, bytesStoreLiteChunksResolve evm]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreLiteConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) ⟨0⟩)
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStoreLitePushChunkEmptyPushArrayShortPacked_of_ne {evm : EVM.State}
    (oldLen header len : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  exact bytesStoreLitePushChunkEmptyPushArrayShortPacked_of_post_header (evm := evm)
    oldLen header len hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStoreLitePushChunkShortPushArray_of_post_header {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : oldBytesLen = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen)
        (solidityShortBytesWord value)) := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hpackedLen : checkBytesPacked (chunksDataBase + oldLen) evmLen = true :=
    checkBytesPacked_of_storageLoad_land_one_zero
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
    exact bytesStoreLiteWriteChunkShortPacked (evm := evmLen)
      oldLen header oldBytesLen value hvalueSize
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
      hpackedLen hflag hlen hvalid
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreLiteConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) (solidityShortBytesWord value))
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStoreLitePushChunkShortPushArray_of_ne {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hvalueSize : value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : oldBytesLen = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen)
        (solidityShortBytesWord value)) := by
  exact bytesStoreLitePushChunkShortPushArray_of_post_header (evm := evm)
    oldLen header oldBytesLen value hvalueSize hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStoreLitePushChunkEmptyBodyReturns {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef (some (.bytes ByteArray.empty)) = .ok evm') :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm'
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes ByteArray.empty)
  let solm0 : Frame := { contract := bytesStoreLiteContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
        .ok (.bytes ByteArray.empty) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreLiteConfig solm0 evm' (.arrayLength .storage chunksRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    simpa [solm0, locals0] using bytesStoreLiteChunksArrayLengthEval evm'
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.pushVal hvalue (by simpa [solm0, locals0] using hpush)) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLitePushChunkBodyReturns {evm evm' : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef (some (.bytes value)) = .ok evm') :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm'
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
        .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreLiteConfig solm0 evm' (.arrayLength .storage chunksRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    simpa [solm0, locals0] using bytesStoreLiteChunksArrayLengthEvalValue evm' value
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.pushVal hvalue (by simpa [solm0, locals0] using hpush)) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLitePushChunkBodyRevertsOfPush {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef (some (.bytes value)) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
        .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.pushValStoreRevert hvalue (by simpa [solm0, locals0] using hpush))

theorem bytesStoreLitePushChunkEmptyFlagOfZero_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ I ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)) = ⟨0⟩) :
    UInt256.land
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
      ⟨1⟩ = ⟨0⟩ := by
  rw [bytesStoreLitePushChunkHeaderAfterLengthStoreZero_of_ne
    (oldLen := bytesStoreLiteChunksLengthWord σ I) hne hzero]
  native_decide

theorem bytesStoreLitePushChunkEmptyValidOfZero_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ I ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)) = ⟨0⟩) :
    UInt256.sub
        (UInt256.land
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
  rw [bytesStoreLitePushChunkHeaderAfterLengthStoreZero_of_ne
    (oldLen := bytesStoreLiteChunksLengthWord σ I) hne hzero]
  native_decide

theorem bytesStoreLiteDeleteCurrentShortZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    deleteStorage? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm] using
      bytesStoreLiteCurrentResolveOfGetNone
        (evm := evm) (locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact deleteSolidityBytesShortZero
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) rfl hresolve bytesStoreLiteCurrentLengthBaseSlot hload

theorem bytesStoreLiteDeleteCurrentShortPacked {evm : EVM.State}
    {header len : UInt256} {copy : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "copy" (.bytes copy) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteContract, locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm] using
      bytesStoreLiteCurrentResolveOfGetNone
        (evm := evm) (locals := (∅ : Store).insert "copy" (.bytes copy))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact deleteSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl hresolve bytesStoreLiteCurrentLengthBaseSlot hload hpacked hflag hlen hvalid

theorem bytesStoreLiteReadCurrentShortPackedExists {evm : EVM.State}
    {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray,
      evalExpr? bytesStoreLiteConfig { contract := bytesStoreLiteContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy) ∧ copy.size = len.toNat := by
  exact evalSolidityBytesShortPackedExists
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (solm := { contract := bytesStoreLiteContract, locals := ∅ })
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl (bytesStoreLiteCurrentLengthResolve evm) bytesStoreLiteCurrentLengthBaseSlot
    hload hflag hlen hvalid

theorem bytesStoreLiteWriteCurrentLongPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨0⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWriteCurrentLongPackedAbsent {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evm := by
  exact writeSolidityBytesLongPackedAbsent
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid hmissing

theorem bytesStoreLiteWriteCurrentLongFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evm ⟨0⟩
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
            ⟨0⟩ value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
              (clearSolidityBytesDataWordsFrom evm ⟨0⟩
                (solidityBytesDataWordCount value.size)
                (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
              ⟨0⟩ value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨0⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWriteCurrentShortPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWriteCurrentShortFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 ((len.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0
            ((len.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨0⟩ (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWriteCurrentMalformedLong {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hload hflag hbad

theorem bytesStoreLiteWriteCurrentMalformedShort {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl bytesStoreLiteCurrentLengthBaseSlot hload hflag hbad

theorem bytesStoreLiteSetDecodedValueBytes_size_lt32 {I : ExecutionEnv} {len : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32) :
    (BytesStoreLiteCore.setDecodedValueBytes I).size < 32 := by
  rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload]
  simpa [hlenAbi] using hshort

theorem bytesStoreLiteSetDecodedLength_le_solcMaxU64 {I : ExecutionEnv}
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
      ABI.solcMaxU64 :=
  Nat.le_of_not_gt hlenMax

theorem bytesStoreLiteSetDecodedPayloadSource {I : ExecutionEnv}
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩).toNat +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
      I.calldata.size := by
  rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
  exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload

theorem bytesStoreLiteWriteCurrentDecodedShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes (BytesStoreLiteCore.setDecodedValueBytes I)) =
        .ok (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩
          (solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I))) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hvalueSize : (BytesStoreLiteCore.setDecodedValueBytes I).size < 32 :=
    bytesStoreLiteSetDecodedValueBytes_size_lt32 hlenAbi hpayload hshort
  have hwrite := bytesStoreLiteWriteCurrentShortPacked (evm := evmSolm0)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := BytesStoreLiteCore.setDecodedValueBytes I)
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0] using hwrite

theorem bytesStoreLiteWriteCurrentEmptyShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := bytesStoreLiteWriteCurrentShortPacked (evm := evmSolm0)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := ByteArray.empty)
    (by decide) hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, hshortEmpty] using hwrite

theorem bytesStoreLiteWriteCurrentDecodedShortFromLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let oldLen : UInt256 := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
    writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes (BytesStoreLiteCore.setDecodedValueBytes I)) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0
            ((oldLen.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨0⟩ (solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I))) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hvalueSize : (BytesStoreLiteCore.setDecodedValueBytes I).size < 32 :=
    bytesStoreLiteSetDecodedValueBytes_size_lt32 hlenAbi hpayload hshort
  have hwrite := bytesStoreLiteWriteCurrentShortFromLongPrepared (evm := evmSolm0)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := BytesStoreLiteCore.setDecodedValueBytes I)
    hvalueSize hload hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, oldLen] using hwrite

theorem bytesStoreLiteWriteCurrentMalformedLongOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreLiteWriteCurrentMalformedLong
    (evm := evmSolm0) (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreLiteWriteCurrentMalformedShortOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreLiteWriteCurrentMalformedShort
    (evm := evmSolm0) (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreLiteAssignCurrentOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwrite : writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    assignStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
      evm .storage currentRef (.bytes value) =
        .ok
          ({ contract := bytesStoreLiteContract,
             locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
               (.bytes value) },
           evmCurrent) := by
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
            (.bytes value) }
        evm currentRef = .ok ({ base := "current", steps := [] }, .bytes) := by
    exact bytesStoreLiteCurrentResolveOfGetNone
      (evm := evm)
      (locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value))
      (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreLiteSetBodyReturns {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignCurrent :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evm .storage currentRef (.bytes value) =
          .ok ({ contract := bytesStoreLiteContract,
                 locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) },
              evmCurrent)) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreLiteContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreLiteConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreLiteConfig solm1 evmCurrent (.arrayLength .localVar { base := "copy" }) =
        .ok (.int value.size) := by
    simp [solm1, locals1, locals0, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consNormal
          (ExecStmt.assign hcopy (by simpa [solm1, locals1, locals0] using hassignCurrent)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetBodyReturnsOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  exact bytesStoreLiteSetBodyReturns (evm := evm) (evmCurrent := evmCurrent) (value := value)
    hwv (bytesStoreLiteAssignCurrentOfWrite hwrite)

theorem bytesStoreLiteSetBodyRevertsOfWrite {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body .reverted := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreLiteContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreLiteConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hresolve :
      resolveStorageRef? bytesStoreLiteConfig solm1 evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm1, locals1, locals0] using
      bytesStoreLiteCurrentResolveOfGetNone
        (evm := evm)
        (locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm1 evm .storage currentRef (.bytes value) =
        .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consRevert (ExecStmt.assignStoreRevert hcopy hassign)

theorem bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmCurrent.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmCurrent.accountMap)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

theorem bytesStoreLiteSetRuntimeOfWriteEVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmEvm evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmEvm.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmEvm.accountMap)
    (hState : EVMStateEquiv evmEvm evmCurrent)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
    hCreated hAccounts hState henc

theorem bytesStoreLiteSetRuntimeOfWriteRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value : ByteArray}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .revert) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetBodyRevertsOfWrite
    (evm := evmSolm0) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCurrentLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreLiteContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreLiteCurrentLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ currentLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreLiteCurrentLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreLiteContract, locals := ∅ } evm (some (.int n))) :=
  bytesStoreLiteCurrentLengthBodyReturns hwv (bytesStoreLiteCurrentLengthResolve evm) hlen

theorem bytesStoreLiteCurrentLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ currentLengthGetter.body
      .reverted :=
  bytesStoreLiteCurrentLengthBodyReverts hwv (bytesStoreLiteCurrentLengthResolve evm) hlen

theorem bytesStoreLiteClearCurrentBodyRevertsOfRead {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ clearCurrentTransition.body
      .reverted := by
  have hresolve := bytesStoreLiteCurrentLengthResolve evm
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.letDeclRevert (by
        have hdecode :
            solidityDecodeBytesLengthHeader
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) = .revert :=
          solidityDecodeBytesLengthHeader_revert_of_readStorageBytesLength_revert
            (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
            (er := { base := "current" }) (evm := evm)
            (baseSlot := ⟨0⟩)
            (header := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            rfl bytesStoreLiteCurrentLengthBaseSlot rfl hlen
        exact evalSolidityBytesRevertOfDecodeRevert
          (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
          (solm := { contract := bytesStoreLiteContract, locals := ∅ })
          (evm := evm) (ref := currentRef) (er := { base := "current" })
          (baseSlot := ⟨0⟩)
          (header := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          rfl hresolve bytesStoreLiteCurrentLengthBaseSlot rfl hdecode)))

theorem bytesStoreLiteClearCurrentBodyReturnsZero {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreLiteConfig { contract := bytesStoreLiteContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes ByteArray.empty))
    (hdel :
      deleteStorage? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm' (some (.int 0))) := by
  let solm1 : Frame :=
    { contract := bytesStoreLiteContract,
      locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hret :
      evalExpr? bytesStoreLiteConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int 0) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteClearCurrentBodyReturnsBytes {evm evm' : EVM.State} {copy : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreLiteConfig { contract := bytesStoreLiteContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy))
    (hdel :
      deleteStorage? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm' (some (.int copy.size))) := by
  let solm1 : Frame :=
    { contract := bytesStoreLiteContract,
      locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hret :
      evalExpr? bytesStoreLiteConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int copy.size) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLitePacketLengthResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes) := by
  have hbase :
      (∅ : Store).get? packetDataRef.base = none := by
    simp [packetDataRef]
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := ∅ } evm packetDataRef =
          .ok ({ base := "packet", steps := [.field "data"] } : EvaledStorageRef) := by
    simpa [packetDataRef] using
      (evalStorageRef_field
        (cfg := bytesStoreLiteConfig)
        (solm := { contract := bytesStoreLiteContract, locals := ∅ })
        (evm := evm) (base := "packet") (field := "data"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreLiteContract, storageDecls, packetStructDecl,
      packetStructTy, bytesSt, storageTypeStep?])

theorem bytesStoreLitePacketLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        { base := "packet", steps := [.field "data"] } = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ packetLengthGetter.body
      (.returned { contract := bytesStoreLiteContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreLitePacketLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ packetLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreLitePacketLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        { base := "packet", steps := [.field "data"] } = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ packetLengthGetter.body
      (.returned { contract := bytesStoreLiteContract, locals := ∅ } evm (some (.int n))) :=
  bytesStoreLitePacketLengthBodyReturns hwv (bytesStoreLitePacketLengthResolve evm) hlen

theorem bytesStoreLitePacketLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm ∅ packetLengthGetter.body
      .reverted :=
  bytesStoreLitePacketLengthBodyReverts hwv (bytesStoreLitePacketLengthResolve evm) hlen

def bytesStoreLiteMappedLengthLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreLiteMappedLengthKeyWord I).toNat))

def bytesStoreLiteChunkLengthLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat))

def bytesStoreLiteSetByteLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "index"
    (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat))

theorem bytesStoreLiteSetByteLocals_get_index (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLocals I).get? "index" =
      some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
  rw [bytesStoreLiteSetByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_self]

theorem bytesStoreLiteSetByteLocals_getElem_index (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLocals I)["index"]? =
      some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using bytesStoreLiteSetByteLocals_get_index I

theorem bytesStoreLiteSetByteLocals_get_current_none (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLocals I).get? "current" = none := by
  rw [bytesStoreLiteSetByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreLiteSetByteLocals_getElem_current_none (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLocals I)["current"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using bytesStoreLiteSetByteLocals_get_current_none I

theorem bytesStoreLiteMappedLengthResolve (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreLiteMappedLengthRef I, .bytes) := by
  have hbase :
      (bytesStoreLiteMappedLengthLocals I).get? "mapped" = none := by
    simp [bytesStoreLiteMappedLengthLocals]
  have hgetKey :
      (bytesStoreLiteMappedLengthLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreLiteMappedLengthKeyWord I).toNat)) := by
    simp [bytesStoreLiteMappedLengthLocals]
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
        evm (mappedRef (.var "key")) =
          .ok (bytesStoreLiteMappedLengthRef I) := by
    exact evalStorageRef_mindex_var_of_get?
      (base := "mapped") hgetKey (by simp [valueToKey?])
  exact resolveStorageRef?_ok hbase her (by
    simp [bytesStoreLiteMappedLengthRef, storageTypeAt?, bytesStoreLiteContract,
      storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreLiteChunkLengthArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    arrayIndexInBounds? bytesStoreLiteConfig evm bytesStoreLiteContract.storage "chunks" []
      (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) = .ok () := by
  simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteStorageLayout,
    solidityStorageLayout, bytesStoreLiteLayout, bytesStoreLiteContract, storageDecls, bytesSt,
    bytesStoreLiteStorageLocLoad_uint256, hbound]

theorem bytesStoreLiteChunkLengthArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    arrayIndexInBounds? bytesStoreLiteConfig evm bytesStoreLiteContract.storage "chunks" []
      (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) = .revert := by
  have hle :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (bytesStoreLiteChunkLengthIndexWord I).toNat :=
    Nat.le_of_not_gt hbound
  simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteStorageLayout,
    solidityStorageLayout, bytesStoreLiteLayout, bytesStoreLiteContract, storageDecls, bytesSt,
    bytesStoreLiteStorageLocLoad_uint256, hle]

theorem bytesStoreLiteChunkLengthEvalStorageRef_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .ok (bytesStoreLiteChunkLengthRef I) := by
  have hgetIndex :
      (bytesStoreLiteChunkLengthLocals I).get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) := by
    simp [bytesStoreLiteChunkLengthLocals]
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm bytesStoreLiteContract.storage "chunks" []
        (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) = .ok () :=
    bytesStoreLiteChunkLengthArrayIndexInBounds_ok evm I hbound
  simpa [chunkRef, bytesStoreLiteChunkLengthRef] using
    (evalStorageRef_aindex_var_of_get?_ok
      (cfg := bytesStoreLiteConfig)
      (solm := { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I })
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreLiteChunkLengthEvalStorageRef_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalStorageRef bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreLiteChunkLengthLocals I).get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) := by
    simp [bytesStoreLiteChunkLengthLocals]
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm bytesStoreLiteContract.storage "chunks" []
        (.int (Int.ofNat (bytesStoreLiteChunkLengthIndexWord I).toNat)) = .revert :=
    bytesStoreLiteChunkLengthArrayIndexInBounds_revert evm I hbound
  simpa [chunkRef] using
    (evalStorageRef_aindex_var_of_get?_revert
      (cfg := bytesStoreLiteConfig)
      (solm := { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I })
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreLiteChunkLengthResolve (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreLiteChunkLengthRef I, .bytes) := by
  have hbase :
      (bytesStoreLiteChunkLengthLocals I).get? "chunks" = none := by
    simp [bytesStoreLiteChunkLengthLocals]
  exact resolveStorageRef?_ok hbase
    (bytesStoreLiteChunkLengthEvalStorageRef_ok evm I hbound)
    (by
      simp [bytesStoreLiteChunkLengthRef, storageTypeAt?, bytesStoreLiteContract,
        storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreLiteChunkLengthResolveReverts (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
      resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreLiteChunkLengthLocals I).get? "chunks" = none := by
    simp [bytesStoreLiteChunkLengthLocals]
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks
    (bytesStoreLiteChunkLengthEvalStorageRef_revert evm I hbound)

theorem bytesStoreLiteMappedLengthBodyReturns {evm : EVM.State} {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreLiteMappedLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteMappedLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
        evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreLiteMappedLengthBodyReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreLiteMappedLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteMappedLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreLiteMappedLengthBodyReturnsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteMappedLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
        evm (some (.int n))) :=
  bytesStoreLiteMappedLengthBodyReturns hwv (bytesStoreLiteMappedLengthResolve evm I) hlen

theorem bytesStoreLiteMappedLengthBodyRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteMappedLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body .reverted :=
  bytesStoreLiteMappedLengthBodyReverts hwv (bytesStoreLiteMappedLengthResolve evm I) hlen

theorem bytesStoreLiteChunkLengthBodyReturns {evm : EVM.State} {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreLiteChunkLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteChunkLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
        evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreLiteChunkLengthBodyReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreLiteChunkLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteChunkLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreLiteChunkLengthBodyBoundsReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, EvalResult.bind, bind])))

theorem bytesStoreLiteChunkLengthBodyReturnsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteChunkLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
        evm (some (.int n))) :=
  bytesStoreLiteChunkLengthBodyReturns hwv
    (bytesStoreLiteChunkLengthResolve evm I hbound) hlen

theorem bytesStoreLiteChunkLengthBodyRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteChunkLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted :=
  bytesStoreLiteChunkLengthBodyReverts hwv
    (bytesStoreLiteChunkLengthResolve evm I hbound) hlen

theorem bytesStoreLiteChunkLengthBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted :=
  bytesStoreLiteChunkLengthBodyBoundsReverts hwv
    (bytesStoreLiteChunkLengthResolveReverts evm I hbound)

theorem bytesStoreLitePacketTagBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "packet" = none) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm locals packetTagGetter.body
      (.returned { contract := bytesStoreLiteContract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef bytesStoreLiteConfig
          { contract := bytesStoreLiteContract, locals := locals } evm packetTagRef =
          .ok { base := "packet", steps := [.field "tag"] } := by
        simpa [packetTagRef] using
          (evalStorageRef_field
            (cfg := bytesStoreLiteConfig)
            (solm := { contract := bytesStoreLiteContract, locals := locals })
            (evm := evm) (base := "packet") (field := "tag"))
      have hty : storageTypeAt? bytesStoreLiteContract.storage
          ({ base := "packet", steps := [.field "tag"] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      have hloc : (bytesStoreLiteConfig.storage.layout
          { base := "packet", steps := [.field "tag"] }) =
          fun _ => some (uint256Loc ⟨3⟩) := by
        funext evm'
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
        (hty := hty) (hloc := hloc)]
      rw [bytesStoreLiteStorageLocLoad_uint256])

theorem bytesStoreLiteX_returnWord263 {cA gh bl σ σ₀ A I} {g : Sat256} {val : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [val, bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

noncomputable def bytesStoreLiteReturnFromMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem bytesStoreLiteReturnFromMem_size (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (bytesStoreLiteReturnFromMem mem val).size = 160 := by
  unfold bytesStoreLiteReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    show (USize.ofNat (128 - mem.size)).toNat = 32 from by
      rw [hsize]
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size, hsize]

theorem bytesStoreLiteReturnFromMem_read64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (bytesStoreLiteReturnFromMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold bytesStoreLiteReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, hsize, ByteArray.size_append, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
      toByteArray_size]
    omega)]
  rw [extract_append_left mem
      (ffi.ByteArray.zeroes (USize.ofNat (128 - mem.size)) ++ UInt256.toByteArray val)
      64 96 (by rw [hsize])]
  rw [← readWithPadding_eq_extract' mem 64 32 (by norm_num) (by norm_num) (by rw [hsize])]
  exact hread64

theorem bytesStoreLiteReturnFromMem_mload64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bytesStoreLiteReturnFromMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((bytesStoreLiteReturnFromMem mem val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [bytesStoreLiteReturnFromMem_size mem val hsize]; decide)
    (by decide)
    (bytesStoreLiteReturnFromMem_read64 mem val hsize hread64)

theorem bytesStoreLiteReturnFromMem_read128 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (bytesStoreLiteReturnFromMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [bytesStoreLiteReturnFromMem_size mem val hsize])]
  unfold bytesStoreLiteReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (USize.ofNat (128 - mem.size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, hsize, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, hsize, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

theorem bytesStoreLiteWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

theorem bytesStoreLiteX_returnWord263OfMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [val, bytesStoreLiteSelWord I] mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (bytesStoreLiteReturnFromMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreLiteReturnFromMem_mload64 mem val hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreLiteReturnFromMem_read128 mem val hsize])
      (by evm_ov)]

theorem bytesStoreLiteX_returnWord263OfMemState {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [val, bytesStoreLiteSelWord I] mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (bytesStoreLiteReturnFromMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreLiteReturnFromMem_mload64 mem val hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreLiteReturnFromMem_read128 mem val hsize])
      (by evm_ov)]

theorem bytesStoreLiteX_packetTag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (packetTagWord σ I)) := by
  obtain ⟨_, _, rd433⟩ := hreach
  have rd437 := evm_run rd433 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd438₀⟩ := rd437.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd438⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨437⟩
        [packetTagWord σ I, bytesStoreLiteSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [packetTagWord, initState] using rd438₀⟩
  have rd263 := evm_run rd438 with [
    push2 ⟨263⟩, jump (by native_decide)]
  exact bytesStoreLiteX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreLiteX_currentLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨1393⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd441⟩ := hreach
  have rd1380 := evm_run rd441 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1380⟩, jump (by native_decide)]
  have rd1384 := evm_run rd1380 with [
    jumpdest, push0, push0, dup1]
  obtain ⟨_, _, rd1385₀⟩ := rd1384.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1385⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1385⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1385₀⟩
  exact ⟨_, _, evm_run rd1385 with [
    push2 ⟨1393⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_clearCurrentReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨1413⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd449⟩ := hreach
  have rd1399 := evm_run rd449 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1399⟩, jump (by native_decide)]
  have rd1404 := evm_run rd1399 with [
    jumpdest, push0, push0, push0, dup1]
  obtain ⟨_, _, rd1405₀⟩ := rd1404.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1405⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1405₀⟩
  exact ⟨_, _, evm_run rd1405 with [
    push2 ⟨1413⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_packetLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLitePacketLengthHeaderWord σ I, ⟨1393⟩, ⟨2⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd476⟩ := hreach
  have rd1628 := evm_run rd476 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1628⟩, jump (by native_decide)]
  have rd1635 := evm_run rd1628 with [
    jumpdest, push0, push1 ⟨2⟩, push0, add, dup1]
  obtain ⟨_, _, rd1636₀⟩ := rd1635.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1636⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1636⟩
        [bytesStoreLitePacketLengthHeaderWord σ I, ⟨2⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLitePacketLengthHeaderWord, initState] using rd1636₀⟩
  exact ⟨_, _, evm_run rd1636 with [
    push2 ⟨1393⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLite_shiftRight_one_eq_div_two (w : UInt256) :
    UInt256.shiftRight w ⟨1⟩ = UInt256.div w ⟨2⟩ := by
  apply u256_inj
  simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Nat.shiftRight_eq_div_pow]
  norm_num [UInt256.size]

theorem bytesStoreLite_shiftRight_five_eq_div_thirtyTwo (w : UInt256) :
    UInt256.shiftRight w ⟨5⟩ = UInt256.div w ⟨32⟩ := by
  apply u256_inj
  simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Nat.shiftRight_eq_div_pow]
  norm_num [UInt256.size]

theorem bytesStoreLiteX_bytesLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteX_bytesLengthDecoderLongValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteX_bytesLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteX_bytesLengthDecoderShortValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteX_currentLengthMalformedPanic {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 bytesStoreLiteFullPanic22Mem1 (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 bytesStoreLiteFullPanic22Mem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_malformedPanicMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanic22MemFrom mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_malformedPanicMem6 {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanic22MemFrom mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_malformedPanicMemCarried {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanic22MemFrom mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_setShortNonemptyMalformedPanic {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {stk : List UInt256}
    (_hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty
      (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hawGe : 5 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat :=
    BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0
      (bytesStoreLiteFullPanic22Mem1From
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [BytesStoreLiteCore.set_mstoreCostSpec
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (off := ⟨0⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (BytesStoreLiteCore.setHelperEntryAw len).toNat 0 32)) -
            Cₘ (BytesStoreLiteCore.setHelperEntryAw len) = 0
        rw [BytesStoreLiteCore.set_activeWordsMstore0_eq_self
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (BytesStoreLiteCore.set_activeWordsMstore0_eq_self
        (aw := BytesStoreLiteCore.setHelperEntryAw len) (by omega))
      (by omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0
      (bytesStoreLiteFullPanic22MemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [BytesStoreLiteCore.set_mstoreCostSpec
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (off := ⟨4⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (BytesStoreLiteCore.setHelperEntryAw len).toNat 4 32)) -
            Cₘ (BytesStoreLiteCore.setHelperEntryAw len) = 0
        rw [BytesStoreLiteCore.set_activeWordsMstore4_eq_self
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (BytesStoreLiteCore.set_activeWordsMstore4_eq_self
        (aw := BytesStoreLiteCore.setHelperEntryAw len) (by omega))
      (by omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide)
      (by
        intro s haw' hstk
        rw [BytesStoreLiteCore.set_revertCostSpec
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (off := ⟨0⟩)
          (len := ⟨36⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (BytesStoreLiteCore.setHelperEntryAw len).toNat 0 36)) -
            Cₘ (BytesStoreLiteCore.setHelperEntryAw len) = 0
        rw [BytesStoreLiteCore.set_activeWordsRevert0_36_eq_self
          (aw := BytesStoreLiteCore.setHelperEntryAw len) (by omega)]
        simp)
      (by omega)]

theorem bytesStoreLiteX_panic32Mem {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_bytesLengthDecoderLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_currentLengthMalformedPanic ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderLongMalformedMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMem ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderLongMalformedMemCarried
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMemCarried ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_currentLengthMalformedPanic ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderShortMalformedMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMem ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderShortMalformedMemCarried
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMemCarried ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderLongMalformedMem6 {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMem6 ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderShortMalformedMem6 {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_malformedPanicMem6 ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_currentLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderLongValid
    (bytesStoreLiteX_currentLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_currentLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderShortValid
    (bytesStoreLiteX_currentLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_currentLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1393⟩ := hdecoded
  have rd263 := evm_run rd1393 with [
    jumpdest, swap3, swap2, pop, pop, jump (by native_decide)]
  exact bytesStoreLiteX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreLiteX_currentLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreLiteX_currentLengthReturnFromDecoded
    (bytesStoreLiteX_currentLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreLiteX_currentLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreLiteX_currentLengthReturnFromDecoded
    (bytesStoreLiteX_currentLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreLiteX_currentLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformed
    (bytesStoreLiteX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_currentLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformed
    (bytesStoreLiteX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_clearCurrentLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformed
    (bytesStoreLiteX_clearCurrentReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_clearCurrentShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformed
    (bytesStoreLiteX_clearCurrentReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_clearCurrentZeroReachCopyDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨1457⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1413⟩ := hdecoded
  have rd1436 := evm_run rd1413 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 currentLengthZeroAllocMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by native_decide) (by evm_ov)]
  have rd1446 := evm_run rd1436 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 currentLengthZeroMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd1448 := evm_run rd1446 with [dup1]
  obtain ⟨_, _, rd1449₀⟩ := rd1448.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1449⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1449₀⟩
  exact ⟨_, _, evm_run rd1449 with [
    push2 ⟨1457⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_clearCurrentZeroReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨1457⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1457₀⟩ := hdecoded
  obtain ⟨_, _, rd1457⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
        [⟨0⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨263⟩, bytesStoreLiteSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1457₀⟩
  have rd1464 := evm_run rd1457 with [jumpdest, dup1, iszero, push2 ⟨1532⟩]
  have rd1532 := rd1464.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have rd1541 := evm_run rd1532 with [
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd1542 := evm_run rd1541 with [
    raw mload 0 ⟨0⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      currentLengthZeroMem_mload128
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd1542 with [
    swap2, pop, push0, push0, push2 ⟨1555⟩, swap2, swap1, push2 ⟨1732⟩,
    jump (by native_decide)]⟩

theorem bytesStoreLiteX_clearCurrentDeleteShortZero {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [⟨0⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd1732⟩ := hreach
  have rd1735pre := evm_run rd1732 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd1736₀⟩ := rd1735pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1736⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1736₀⟩
  have hdecode := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1736 with [
      push2 ⟨1744⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ I) (ret := ⟨1744⟩)
    (rest := [⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hflag
    hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1744₀⟩ := hdecode
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1744₀⟩
  have rd1748pre := evm_run rd1744 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd1748₀⟩ := rd1748pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1748⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1748⟩
        [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd1748₀⟩
  have rd1756 := evm_run rd1748 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1759⟩]
  have rd1756' := rd1756.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1555 := evm_run rd1756' with [pop, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd1555 with [jumpdest, pop, swap1, jump (by native_decide)]⟩

theorem bytesStoreLiteX_clearCurrentZeroReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [⟨0⟩, bytesStoreLiteSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      currentLengthZeroMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 3 currentLengthZeroReturnMem (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload64
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨160⟩) ⟨160⟩).toNat = 32 from by decide,
          currentLengthZeroReturnMem_read160])
      (by evm_ov)]

theorem bytesStoreLiteX_clearCurrentShortZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  have hdecoded₀ := bytesStoreLiteX_bytesLengthDecoderShortValid
    (hreach := bytesStoreLiteX_clearCurrentReachDecoder hreach)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ I) (ret := ⟨1413⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I])
    hflag
    hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1413₀⟩ := hdecoded₀
  have hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1413₀⟩
  have hcopy := bytesStoreLiteX_clearCurrentZeroReachCopyDecoder hdecoded
  have hdelStart := bytesStoreLiteX_clearCurrentZeroReachDelete hcopy
    hflag hvalid hzero
  exact bytesStoreLiteX_clearCurrentZeroReturnFromWrapper
    (bytesStoreLiteX_clearCurrentDeleteShortZero hperm hdelStart hflag hvalid hzero)

theorem bytesStoreLiteX_clearCurrentShortReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreLiteSelWord I]
      (currentLengthPayloadMem len (bytesStoreLiteCurrentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  have hvalidHeader :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded₀ := bytesStoreLiteX_bytesLengthDecoderShortValid
    (hreach := bytesStoreLiteX_clearCurrentReachDecoder hreach)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ I) (ret := ⟨1413⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I])
    hflag hvalidHeader (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1413₀⟩ := hdecoded₀
  obtain ⟨_, _, rd1413⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1413₀⟩
  have rd1436 := evm_run rd1413 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by native_decide) (by evm_ov)]
  have rd1446 := evm_run rd1436 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd1448 := evm_run rd1446 with [dup1]
  obtain ⟨_, _, rd1449₀⟩ := rd1448.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1449⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1449₀⟩
  have hdecode := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1449 with [
      push2 ⟨1457⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ I) (ret := ⟨1457⟩)
    (rest := [⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1457₀⟩ := hdecode
  obtain ⟨_, _, rd1457⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreLiteSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1457₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotZero : UInt256.isZero len = ⟨0⟩ := isZero_eq_zero_of_ne hnonzero
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd1464 := evm_run rd1457 with [jumpdest, dup1, iszero, push2 ⟨1532⟩]
  have rd1465 := rd1464.jumpiNT (by native_decide) hnotZero (by evm_ov)
  have rd1491 := evm_run rd1465 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1491⟩]
  have rd1472 := rd1491.jumpiNT (by native_decide) hnotGt31 (by evm_ov)
  have rd1477pre := evm_run rd1472 with [push2 ⟨256⟩, dup1, dup4]
  obtain ⟨_, _, rd1478₀⟩ := rd1477pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1478⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1478⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨256⟩, ⟨256⟩, len, ⟨0⟩, ⟨160⟩, len,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1478₀⟩
  have rd1482 := evm_run rd1478 with [
    div, mul, dup4,
    raw mstore 3 (currentLengthPayloadMem len (bytesStoreLiteCurrentLengthHeaderWord σ I))
      (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov)]
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have rd1532 := evm_run rd1482 with [
    swap2, push1 ⟨32⟩, add, swap2, push2 ⟨1532⟩, jump (by native_decide),
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1,
    raw mload 0 len (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (currentLengthPayloadMem_mload128 len (bytesStoreLiteCurrentLengthHeaderWord σ I))
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [hfree] using
      (evm_run rd1532 with [
        swap2, pop, push0, push0, push2 ⟨1555⟩, swap2, swap1, push2 ⟨1732⟩,
        jump (by native_decide)])⟩

theorem bytesStoreLiteX_clearCurrentDeleteShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreLiteSelWord I]
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd1732⟩ := hreach
  have rd1735pre := evm_run rd1732 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd1736₀⟩ := rd1735pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1736⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩,
          bytesStoreLiteSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1736₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecode := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1736 with [
      push2 ⟨1744⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ I) (ret := ⟨1744⟩)
    (rest := [⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := mem) (aw := aw) (rdata := rdata)
    hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1744₀⟩ := hdecode
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1744₀⟩
  have rd1748pre := evm_run rd1744 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd1748₀⟩ := rd1748pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1748⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1748⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd1748₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd1756 := evm_run rd1748 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1759⟩]
  have rd1756' := rd1756.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1555 := evm_run rd1756' with [pop, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd1555 with [jumpdest, pop, swap1, jump (by native_decide)]⟩

theorem bytesStoreLiteX_clearCurrentShortReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreLiteSelWord I]
      (currentLengthPayloadMem len (bytesStoreLiteCurrentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C)
    (hfree : currentLengthFreePtr len = ⟨192⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (currentLengthPayloadMem_mload64 len (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨192⟩ hfree)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 3 (currentLengthPayloadReturnMem len (bytesStoreLiteCurrentLengthHeaderWord σ I))
      (UInt256.ofNat 7) (by native_decide)
      mem_cost
      (by rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost
      (currentLengthPayloadReturnMem_mload64 len (bytesStoreLiteCurrentLengthHeaderWord σ I)
        ⟨192⟩ hfree)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by native_decide)
      mem_cost
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨192⟩) ⟨192⟩).toNat = 32 from by decide,
          currentLengthPayloadReturnMem_read192])
      (by evm_ov)]

theorem bytesStoreLiteX_clearCurrentShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have hdelStart := bytesStoreLiteX_clearCurrentShortReachDelete
    (g := g) hreach hflag hlen hvalid hnonzero
  have hdel := bytesStoreLiteX_clearCurrentDeleteShortValid
    (g := g) hperm hdelStart hflag hlen hvalid
  exact bytesStoreLiteX_clearCurrentShortReturnFromWrapper hdel hfree

theorem bytesStoreLiteX_packetLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩, ⟨2⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderLongValid
    (bytesStoreLiteX_packetLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_packetLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨2⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderShortValid
    (bytesStoreLiteX_packetLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_packetLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [len, ⟨2⟩, ⟨0⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1393⟩ := hdecoded
  have rd263 := evm_run rd1393 with [
    jumpdest, swap3, swap2, pop, pop, jump (by native_decide)]
  exact bytesStoreLiteX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreLiteX_packetLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreLiteX_packetLengthReturnFromDecoded
    (bytesStoreLiteX_packetLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreLiteX_packetLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreLiteX_packetLengthReturnFromDecoded
    (bytesStoreLiteX_packetLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreLiteX_packetLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformed
    (bytesStoreLiteX_packetLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_packetLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformed
    (bytesStoreLiteX_packetLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_mappedLengthDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd376⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have rd2131 := evm_run rd376 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨390⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  have rd2147 := evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd390 := evm_run rd2147 with [
    jumpdest, pop, calldataload, swap2, swap1, pop, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreLiteMappedLengthKeyWord I from rfl] at rd390
  exact ⟨_, _, evm_run rd390 with [
    jumpdest, push2 ⟨1113⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_mappedLengthDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd376⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  have rd2131 := evm_run rd376 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨390⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  exact evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_mappedLengthDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd376⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  have rd2131 := evm_run rd376 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨390⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  exact evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_chunkLengthDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd503⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have rd2131 := evm_run rd503 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨517⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  have rd2147 := evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd517 := evm_run rd2147 with [
    jumpdest, pop, calldataload, swap2, swap1, pop, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreLiteChunkLengthIndexWord I from rfl] at rd517
  exact ⟨_, _, evm_run rd517 with [
    jumpdest, push2 ⟨1693⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_chunkLengthDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd503⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  have rd2131 := evm_run rd503 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨517⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  exact evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_chunkLengthDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd503⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  have rd2131 := evm_run rd503 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨517⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2131⟩, jump (by native_decide)]
  exact evm_run rd2131 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2147⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  exact evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  exact evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiNT (by rw [hgt']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffSmall : (calldataWord I.calldata 4).toNat < 2 ^ 255 := by
    have hle : (calldataWord I.calldata 4).toNat ≤ ABI.solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hstartPlus31Small :
      4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255 := by
    have hle : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
      simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        exact hstartPlus31Small
    · apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        exact hstartPlus31Small
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hlenMax
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiNT (by rw [hlenMax']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hpayload
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  exact evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiNT (by rw [hpayload']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiNT (by rw [hgt']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLeMax : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        omega
    · apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hlenMax
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiNT (by rw [hlenMax']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hpayload
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  exact evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiNT (by rw [hpayload']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_pushChunkDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd457⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hpayload
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  have rd1876 := evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiT (by rw [hpayload']; decide) (by native_decide)]
  have rd1934 := evm_run rd1876 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by native_decide)]
  have rd471 := evm_run rd1934 with [
    jumpdest, swap1, swap7, swap1, swap6, pop, swap4, pop, pop, pop, pop,
    jump (by native_decide)]
  exact ⟨_, _, by
    simpa [calldataWord] using
      (evm_run rd471 with [jumpdest, push2 ⟨1559⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hpayload
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  have rd1876 := evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiT (by rw [hpayload']; decide) (by native_decide)]
  have rd1934 := evm_run rd1876 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by native_decide)]
  have rd258 := evm_run rd1934 with [
    jumpdest, swap1, swap7, swap1, swap6, pop, swap4, pop, pop, pop, pop,
    jump (by native_decide)]
  exact ⟨_, _, by
    simpa [calldataWord] using
      (evm_run rd258 with [jumpdest, push2 ⟨522⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setReachStorageWriteMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2388⟩
        [⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
        (BytesStoreLiteCore.setHelperEntryAw len)
        ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd522⟩ := hreach
  have rd566 := evm_run rd522 with [
    jumpdest, push0, push0, dup4, dup4, dup1, dup1, push1 ⟨31⟩, add,
    push1 ⟨32⟩, dup1, swap2, div, mul, push1 ⟨32⟩, add,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (BytesStoreLiteCore.currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        rfl)
      (by decide) (by evm_ov),
    dup1, swap4, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (BytesStoreLiteCore.currentLengthMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup4, dup4, dup1, dup3, dup5]
  let awCopy : UInt256 :=
    UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)
  have hawCopy :
      UInt256.ofNat
          (MachineState.M (UInt256.ofNat 5).toNat (⟨160⟩ : UInt256).toNat
            len.toNat) =
        awCopy := by
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  have rd567 := RD.calldatacopy
    (Cₘ awCopy - Cₘ (UInt256.ofNat 5))
    (BytesStoreLiteCore.setCalldataMem I.calldata len payloadStart)
    awCopy
    rd566 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy]
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 from by decide])
    (by
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 from by decide]
      rfl)
    hawCopy
    (by evm_ov)
  have rd571 := evm_run rd567 with [push0, swap3, add, dup3, swap1]
  let awPad : UInt256 :=
    UInt256.ofNat (MachineState.M awCopy.toNat (((⟨160⟩ : UInt256) + len).toNat) 32)
  have rd573 := RD.mstore
    (Cₘ awPad - Cₘ awCopy)
    (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    awPad
    rd571 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy, awPad]
      rw [show ((⟨32⟩ : UInt256) + ⟨128⟩ + len) = ((⟨160⟩ : UInt256) + len) from by
        rw [show ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ from by decide]])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd2388 := evm_run rd573 with [
    pop, swap4, swap5, pop, push2 ⟨592⟩, swap3, pop,
    dup5, swap2, pop, dup4, swap1, pop, push2 ⟨2388⟩,
    jump (by native_decide)]
  exact ⟨_, _, by
    simpa [BytesStoreLiteCore.setCalldataMem, BytesStoreLiteCore.setPaddedMem,
      BytesStoreLiteCore.setHelperEntryAw, awCopy, awPad,
      BytesStoreLiteCore.currentLengthAllocSize, BytesStoreLiteCore.currentLengthFreePtr]
      using rd2388⟩

theorem bytesStoreLiteX_setReachWriteHeaderDecoderNonempty {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [BytesStoreLiteCore.currentLengthHeaderWord σ I, ⟨2428⟩, len, ⟨2434⟩, len,
        ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2388⟩ := bytesStoreLiteX_setReachStorageWriteMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach
  have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    simpa [ABI.solcMaxU64] using hlenMax
  have rd2391 := evm_run rd2388 with [
    jumpdest, dup2,
    raw mload 0 len (BytesStoreLiteCore.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [BytesStoreLiteCore.set_activeWordsMload128_eq_self
          (BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 hlenMax)]
        simp)
      (BytesStoreLiteCore.setPaddedMem_mload128_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (BytesStoreLiteCore.set_activeWordsMload128_eq_self
        (BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 hlenMax))
      (by evm_ov)]
  have rd2400 := RD.pushConst rd2391 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2414 := evm_run rd2400 with [
    dup2, gt, iszero, push2 ⟨2414⟩,
    jumpiT (by rw [hgtMax]; decide) (by native_decide)]
  have rd2423pre := evm_run rd2414 with [
    jumpdest, push2 ⟨2434⟩, dup2, push2 ⟨2428⟩, dup5]
  obtain ⟨_, _, rd2423₀⟩ := rd2423pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2424⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
        [BytesStoreLiteCore.currentLengthHeaderWord σ I, ⟨2428⟩, len, ⟨2434⟩, len,
          ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
        (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [BytesStoreLiteCore.currentLengthHeaderWord, initState] using rd2423₀⟩
  exact ⟨_, _, evm_run rd2424 with [push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_pushChunkIncrementLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1573⟩
      [bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  obtain ⟨_, _, rd1559⟩ := hreach
  have rd1563pre := evm_run rd1559 with [jumpdest, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd1564₀⟩ := rd1563pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1564⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1564⟩
        [bytesStoreLiteChunksLengthWord σ I, ⟨1⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteChunksLengthWord, initState] using rd1564₀⟩
  have rd1568pre := evm_run rd1564 with [dup1, dup3, add, dup3]
  obtain ⟨_, _, rd1569₀⟩ := rd1568pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1569⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1569⟩
        [bytesStoreLiteChunksLengthWord σ I, ⟨1⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
    exact ⟨_, _, by
      simpa [initState, u256_add_comm (bytesStoreLiteChunksLengthWord σ I) (⟨1⟩ : UInt256)]
        using rd1569₀⟩
  exact ⟨_, _, evm_run rd1569 with [
    push0, swap2, dup3,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov)]⟩

private theorem bytesStoreLiteX_pushChunkReachWriteHelper_literal {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {oldLen len payloadStart ret sel : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1573⟩
      [oldLen, ⟨0⟩, len, payloadStart, ret, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2599⟩
      [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + oldLen,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + oldLen,
        ⟨0⟩, len, payloadStart, ret, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1573⟩ := hreach
  have rd1606 := RD.pushConst rd1573
    (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa using
      (evm_run rd1606 with [
        add, push2 ⟨1617⟩, dup4, dup6, dup4, push2 ⟨2599⟩,
        jump (by native_decide)])⟩

private theorem bytesStoreLiteX_pushChunkReachWriteHelperFromBody_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hinc := bytesStoreLiteX_pushChunkIncrementLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreLiteX_pushChunkReachWriteHelper_literal
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (oldLen := bytesStoreLiteChunksLengthWord σ I) (len := len)
    (payloadStart := payloadStart) (ret := ⟨263⟩) (sel := bytesStoreLiteSelWord I) hinc

theorem bytesStoreLiteX_writeBytesHelperReachHeaderDecoder {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2599⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hov : tail.length + 9 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      ((σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: slot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2599⟩ := hreach
  have rd2600 := rd2599.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2609 := RD.pushConst rd2600 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2623 := evm_run rd2609 with [
    dup4, gt, iszero, push2 ⟨2623⟩,
    jumpiT (by rw [hlenMax]; decide) (by native_decide)]
  have rd2633pre := evm_run rd2623 with [jumpdest, push2 ⟨2643⟩, dup4, push2 ⟨2637⟩, dup4]
  obtain ⟨_, _, rd2633₀⟩ := rd2633pre.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [initState] using
      (evm_run rd2633₀ with [push2 ⟨2246⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried {cA gh bl σinit τ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

private theorem bytesStoreLiteX_pushChunkReachWriteHeaderDecoder_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ ::
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
            UInt256) + bytesStoreLiteChunksLengthWord σ I) ::
        payloadStart :: len :: ⟨1617⟩ ::
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
            UInt256) + bytesStoreLiteChunksLengthWord σ I) ::
        ⟨0⟩ :: len :: payloadStart :: ⟨263⟩ :: bytesStoreLiteSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hhelper := bytesStoreLiteX_pushChunkReachWriteHelperFromBody_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreLiteX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_pushChunkReachWriteHeaderDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ::
        payloadStart :: len :: ⟨1617⟩ :: (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ::
        ⟨0⟩ :: len :: payloadStart :: ⟨263⟩ :: bytesStoreLiteSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  simpa [bytesStoreLiteChunksDataBaseLiteral] using
    bytesStoreLiteX_pushChunkReachWriteHeaderDecoder_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax

theorem bytesStoreLiteX_setReachWriteHeaderDecoderEmpty {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [BytesStoreLiteCore.currentLengthHeaderWord σ I, ⟨2428⟩, ⟨0⟩, ⟨2434⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2388₀⟩ := bytesStoreLiteX_setReachStorageWriteMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := (⟨0⟩ : UInt256)) (payloadStart := payloadStart) hreach
  obtain ⟨_, _, rd2388⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2388⟩
        [⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
          ⟨263⟩, bytesStoreLiteSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [currentLengthZeroReturnMem, BytesStoreLiteCore.currentLengthZeroReturnMem,
        BytesStoreLiteCore.setCalldataMem, BytesStoreLiteCore.setPaddedMem,
        BytesStoreLiteCore.setHelperEntryAw, BytesStoreLiteCore.currentLengthAllocSize,
        BytesStoreLiteCore.currentLengthFreePtr] using rd2388₀⟩
  have rd2391 := evm_run rd2388 with [
    jumpdest, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by native_decide) (by evm_ov)]
  have rd2400 := RD.pushConst rd2391 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2414 := evm_run rd2400 with [
    dup2, gt, iszero, push2 ⟨2414⟩,
    jumpiT (by decide) (by native_decide)]
  have rd2423pre := evm_run rd2414 with [
    jumpdest, push2 ⟨2434⟩, dup2, push2 ⟨2428⟩, dup5]
  obtain ⟨_, _, rd2424₀⟩ := rd2423pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2424⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
        [BytesStoreLiteCore.currentLengthHeaderWord σ I, ⟨2428⟩, ⟨0⟩, ⟨2434⟩,
          ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [BytesStoreLiteCore.currentLengthHeaderWord, initState] using rd2424₀⟩
  exact ⟨_, _, evm_run rd2424 with [push2 ⟨2246⟩, jump (by native_decide)]⟩

private theorem bytesStoreLiteX_pushChunkLongMalformed_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                        UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_pushChunkReachWriteHeaderDecoder_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (header :=
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)))
    (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I,
      payloadStart, len, ⟨1617⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (by simpa using hdecoder)
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreLiteX_pushChunkLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hflag
  have hbad' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                        UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hbad
  exact bytesStoreLiteX_pushChunkLongMalformed_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag' hbad'

private theorem bytesStoreLiteX_pushChunkShortMalformed_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_pushChunkReachWriteHeaderDecoder_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (header :=
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)))
    (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I,
      payloadStart, len, ⟨1617⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (by simpa using hdecoder)
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreLiteX_pushChunkShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hflag
  have hbad' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hbad
  exact bytesStoreLiteX_pushChunkShortMalformed_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag' hbad'

theorem bytesStoreLiteX_writeBytesHelperShortHeaderReachCleanup {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2599⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD slot ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot ::
        UInt256.land
          (UInt256.div
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
            ⟨2⟩)
          ⟨127⟩ ::
        len :: ⟨2643⟩ :: slot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, σ) k C := by
  let header : UInt256 :=
    σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)
  have hdecReach := bytesStoreLiteX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata) hreach hlenMax
    (by omega)
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := len :: ⟨2643⟩ :: slot :: payloadStart :: len :: ret :: tail)
    (mem := mem) (aw := aw) (rdata := rdata)
    (by simpa [header] using hdecReach)
    (by simpa [header] using hflag)
    (by simpa [header] using hvalid)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2637⟩ := hdecoded
  exact ⟨_, _, evm_run rd2637 with [
    jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_writeBytesCleanupOldShort {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : tail.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret tail mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd1809 := rd2308.jumpiT (by native_decide)
    (by rw [holdNotLong]; decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd1809 with [
    jumpdest, pop, pop, pop, raw jump (by native_decide) hret
      (by omega)]⟩

theorem bytesStoreLiteX_writeBytesCleanupOldLongNoClear {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : tail.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret tail mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2310 := rd2308.jumpiNT (by native_decide)
    (by rw [holdLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2318 := evm_run rd2310 with [dup3, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd1809 := rd2318.jumpiT (by native_decide)
    (by rw [hgtOldNew]; decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd1809 with [
    jumpdest, pop, pop, pop, raw jump (by native_decide) hret
      (by omega)]⟩

theorem bytesStoreLiteX_setCurrentCleanupOldLongShortToLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (⟨0⟩ :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hshort : UInt256.lt len ⟨32⟩ = ⟨1⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (⟨0⟩ ::
        UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩ ::
        (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ::
        ⟨0⟩ :: oldLen :: len :: ret :: tail)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
      (BytesStoreLiteCore.clearCurrentHashAw aw) rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2310 := rd2308.jumpiNT (by native_decide)
    (by rw [holdLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2318 := evm_run rd2310 with [dup3, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2320 := rd2318.jumpiNT (by native_decide)
    (by rw [hgtOldNew]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2343 := evm_run rd2320 with [
    dup1, push0,
    raw mstore (Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw) - Cₘ aw)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
      (BytesStoreLiteCore.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (BytesStoreLiteCore.clearCurrentHashAw aw) -
        Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw))
      BytesStoreLiteCore.clearCurrentBaseWord
      (BytesStoreLiteCore.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentHashAw, BytesStoreLiteCore.clearCurrentBaseAw])
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov),
    push1 ⟨31⟩, dup5, add, push1 ⟨5⟩, shr, push1 ⟨32⟩, dup6, lt, iszero,
    push2 ⟨2345⟩]
  have rd2345 := rd2343.jumpiNT (by native_decide)
    (by rw [hshort]; decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    have hrd := evm_run rd2345 with [
      pop, push0, jumpdest, swap1, dup2, add, swap1, push1 ⟨31⟩, dup5, add,
      push1 ⟨5⟩, shr, sub, push0]
    exact hrd⟩

theorem bytesStoreLiteX_setShortLongHeaderReachCleanupLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2359⟩
      [⟨0⟩, UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩,
        ⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord, ⟨0⟩, oldLen, len, ⟨2434⟩,
        len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, σ) k C := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hvalidHeader :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
        (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < oldLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldLen len = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := len) (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  exact bytesStoreLiteX_setCurrentCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (oldLen := oldLen) (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setLongOldLongNoClearReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hvalidHeader :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
        (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  exact bytesStoreLiteX_writeBytesCleanupOldLongNoClear
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setClearDataWordsLoopDone {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx count = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2359⟩ := hreach
  have hcond : UInt256.isZero (UInt256.lt idx count) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have rd2367 := evm_run rd2359 with [
    jumpdest, dup2, dup2, lt, iszero, push2 ⟨2380⟩]
  have rd2380 := rd2367.jumpiT (by native_decide) hcond (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2380 with [
    jumpdest, pop, pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by omega)]⟩

theorem bytesStoreLiteX_setClearDataWordsLoopStep {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx count) = ⟨0⟩)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (((⟨1⟩ : UInt256) + idx) :: count :: base :: dead₀ :: dead₁ :: dead₂ ::
        ret :: rest)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner τ (idx + base) ⟨0⟩) k C := by
  obtain ⟨_, _, rd2359⟩ := hreach
  have rd2367 := evm_run rd2359 with [
    jumpdest, dup2, dup2, lt, iszero, push2 ⟨2380⟩]
  have rd2368 := rd2367.jumpiNT (by native_decide) hcontinue
    (by simp only [List.length_cons]; omega)
  have rd2372pre := evm_run rd2368 with [push0, dup4, dup3, add]
  obtain ⟨_, _, rd2373⟩ := rd2372pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2379 := evm_run rd2373 with [push1 ⟨1⟩, add, push2 ⟨2359⟩]
  exact ⟨_, _, rd2379.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)⟩

theorem bytesStoreLiteX_setClearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex idx i) count) =
        ⟨0⟩)
    (hdone : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex idx fuel) count = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [BytesStoreLiteCore.clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        bytesStoreLiteX_setClearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
          (dead₀ := dead₀) (dead₁ := dead₁) (dead₂ := dead₂) (ret := ret)
          (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret hov
  | succ n ih =>
      have hstep := bytesStoreLiteX_setClearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
        (dead₀ := dead₀) (dead₁ := dead₁) (dead₂ := dead₂) (ret := ret)
        (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by
          simpa [BytesStoreLiteCore.clearDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hstep' :
          ∃ k C, RD bytesStoreLiteBytecode I g
            (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
            (((⟨1⟩ : UInt256) + idx) :: count :: base :: dead₀ :: dead₁ :: dead₂ ::
              ret :: rest)
            mem aw rdata (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
        simpa [u256_add_comm idx base] using hstep
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (BytesStoreLiteCore.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i)
              count) =
              ⟨0⟩ := by
        intro i hi
        simpa [BytesStoreLiteCore.clearDataWordsLoopIndex,
          BytesStoreLiteCore.clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.lt
            (BytesStoreLiteCore.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n)
            count =
            ⟨0⟩ := by
        simpa [BytesStoreLiteCore.clearDataWordsLoopIndex,
          BytesStoreLiteCore.clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep' hcontinueTail hdoneTail

theorem bytesStoreLiteX_setShortLongHeaderReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩ fuel) k C := by
  have hloopEntry := bytesStoreLiteX_setShortLongHeaderReachCleanupLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
    hreach hnz hshort hlenMax hsrc hflag holdLen hvalid
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := ⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord)
    (dead₀ := (⟨0⟩ : UInt256)) (dead₁ := oldLen) (dead₂ := len)
    (ret := (⟨2434⟩ : UInt256))
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hloop

theorem bytesStoreLiteX_setShortLongHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_setShortLongHeaderReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
      (fuel := count.toNat)
      hperm hreach hnz hshort hlenMax hsrc hflag holdLen hvalid hcontinue hdone

theorem bytesStoreLiteX_setShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428⟩ := hdecoded
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [oldLen] using
        (evm_run rd2428 with [jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)])⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  exact bytesStoreLiteX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
    (aw := BytesStoreLiteCore.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdNotLong (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteX_setShortNonemptyLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := hdecoder)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setShortNonemptyShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := hdecoder)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setShortNonemptyLongMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hflag
  have hbadCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hbad
  exact bytesStoreLiteX_setShortNonemptyLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflagCore hbadCore

theorem bytesStoreLiteX_setShortNonemptyShortMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hflag
  have hbadCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hbad
  exact bytesStoreLiteX_setShortNonemptyShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflagCore hbadCore

theorem bytesStoreLiteSetShortNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart : UInt256} {value : ByteArray}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreLiteX_setShortNonemptyLongMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hreach hnz hlenMax hsrc hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .revert := by
    have hwrite₀ := bytesStoreLiteWriteCurrentMalformedLongOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreLiteSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    hcode hwv hrev hd hdec (by simpa [evmSolm0] using hwrite)

theorem bytesStoreLiteSetShortNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart : UInt256} {value : ByteArray}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreLiteX_setShortNonemptyShortMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hreach hnz hlenMax hsrc hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .revert := by
    have hwrite₀ := bytesStoreLiteWriteCurrentMalformedShortOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreLiteSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    hcode hwv hrev hd hdec (by simpa [evmSolm0] using hwrite)

theorem bytesStoreLiteSetDecodedNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact BytesStoreLiteCore.decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact bytesStoreLiteSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    exact bytesStoreLiteSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreLiteSetShortNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd
    hdec
    (by simpa [len] using hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreLiteSetDecodedNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact BytesStoreLiteCore.decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact bytesStoreLiteSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    exact bytesStoreLiteSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreLiteSetShortNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd
    hdec
    (by simpa [len] using hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreLiteSetRawDecodedNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  have hlenEvm :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact BytesStoreLiteCore.decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenEvm]
    exact bytesStoreLiteSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    rw [hlenEvm]
    dsimp [payloadStart]
    exact bytesStoreLiteSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreLiteSetShortNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd hdec
    (by rw [hlenEvm]; exact hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreLiteSetRawDecodedNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  have hlenEvm :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact BytesStoreLiteCore.decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenEvm]
    exact bytesStoreLiteSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    rw [hlenEvm]
    dsimp [payloadStart]
    exact bytesStoreLiteSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreLiteSetShortNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd hdec
    (by rw [hlenEvm]; exact hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreLiteSetRawDecodedNonemptyLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hreach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  exact bytesStoreLiteSetRawDecodedNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsel hAccounts hreach
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    hnz hflag hbad

theorem bytesStoreLiteSetRawDecodedNonemptyShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hreach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  exact bytesStoreLiteSetRawDecodedNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsel hAccounts hreach
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    hnz hflag hbad

theorem bytesStoreLiteX_setShortNonemptyWriteHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperPayloadAw len)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord) k C := by
  dsimp only
  obtain ⟨_, _, rd2434⟩ := hreach
  have hnotLong : UInt256.gt len ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hshort
  have hnonzero : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by rw [hzero]; rfl)
  have hlenNotZero : UInt256.isZero len = ⟨0⟩ :=
    isZero_eq_zero_of_ne hnonzero
  have rd2445 := evm_run rd2434 with [
    jumpdest, push1 ⟨32⟩, push1 ⟨31⟩, dup3, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨2484⟩]
  have rd2449 := rd2445.jumpiNT (by native_decide)
    (by
      rw [hnotLong]
      decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2452 := evm_run rd2449 with [push0, dup4, iszero, push2 ⟨2461⟩]
  have rd2456 := rd2452.jumpiNT (by native_decide)
    (by simp [hlenNotZero])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2460pre := evm_run rd2456 with [pop, dup5, dup3, add]
  have haddrWord : ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ := by native_decide
  have haddr : (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 := by native_decide
  have rd2461₀ := RD.mload
    (Cₘ (BytesStoreLiteCore.setHelperPayloadAw len) -
      Cₘ (BytesStoreLiteCore.setHelperEntryAw len))
    (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart)
    (BytesStoreLiteCore.setHelperPayloadAw len)
    rd2460pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        BytesStoreLiteCore.setHelperPayloadAw, haddr])
    (by
      rw [haddrWord]
      rfl)
    (by
      rw [haddrWord]
      rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2479pre := evm_run rd2461₀ with [
    jumpdest, push0, not, push1 ⟨3⟩, dup6, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup5, swap1, shl, lor, dup5]
  obtain ⟨_, _, rd2480₀⟩ := rd2479pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [initState, BytesStoreLiteCore.setHelperPayloadWord,
      BytesStoreLiteCore.setHelperPayloadAw, List.append_assoc] using
      (evm_run rd2480₀ with [
        push2 ⟨2572⟩, jump (by native_decide),
        jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setLongReachLoopFrom2434
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {len payloadStart : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [⟨0⟩, BytesStoreLiteCore.clearCurrentBaseWord,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          ⟨32⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
        (BytesStoreLiteCore.clearCurrentHashAw aw) rdata (cA, τ) k' C' := by
  have hgt31 : UInt256.gt len ⟨31⟩ = ⟨1⟩ := by
    apply ugt_one
    have hge32 : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      (by omega : 31 < len.toNat)
  have rd2445 := evm_run hreach with [
    jumpdest, push1 ⟨32⟩, push1 ⟨31⟩, dup3, gt, push1 ⟨1⟩, dup2, eq,
    push2 ⟨2484⟩]
  have rd2484 := rd2445.jumpiT (by native_decide)
    (by
      rw [hgt31]
      decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd2484 with [
    jumpdest, push0, dup5, dup2,
    raw mstore (Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw) - Cₘ aw)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
      (BytesStoreLiteCore.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup2,
    raw keccak256
      (Cₘ (BytesStoreLiteCore.clearCurrentHashAw aw) -
        Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw))
      BytesStoreLiteCore.clearCurrentBaseWord
      (BytesStoreLiteCore.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentHashAw, BytesStoreLiteCore.clearCurrentBaseAw])
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov),
    push1 ⟨31⟩, not, dup6, and, swap2]⟩

theorem bytesStoreLiteX_setLongDataWordsLoopStep
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx cutoff) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [(⟨32⟩ : UInt256) + idx, (⟨1⟩ : UInt256) + slot, cutoff, gtFlag,
          (⟨32⟩ : UInt256) + stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot word) k' C' := by
  obtain ⟨_, _, rd2499⟩ := hreach
  have rd2508 := evm_run rd2499 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2531⟩,
    jumpiNT hcontinue]
  have rd2511pre := evm_run rd2508 with [dup8, dup6, add]
  have rd2512 := RD.mload mloadCost word awLoad rd2511pre
    (by native_decide)
    (by
      intro s haw hstk
      exact hmloadCost s haw (by simpa [u256_add_comm stride ptr] using hstk))
    (by simpa [u256_add_comm stride ptr] using hmload)
    (by simpa [u256_add_comm stride ptr] using hawLoad)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2513pre := evm_run rd2512 with [dup3]
  obtain ⟨_, _, rd2514₀⟩ := rd2513pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2514⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2514⟩
        [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot word) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd2514₀⟩
  exact ⟨_, _, by
    simpa [u256_add_comm idx ⟨32⟩, u256_add_comm slot ⟨1⟩,
      u256_add_comm stride ⟨32⟩] using
      (evm_run rd2514 with [
        push1 ⟨32⟩, swap5, dup6, add, swap5, push1 ⟨1⟩, swap1,
        swap3, add, swap2, add, push2 ⟨2499⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setLongDataWordsLoopGenerated
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + BytesStoreLiteCore.longDataWordsLoopStride stride i,
          BytesStoreLiteCore.longDataWordsLoopIndex idx i,
          BytesStoreLiteCore.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          BytesStoreLiteCore.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [BytesStoreLiteCore.longDataWordsLoopIndex idx fuel,
          BytesStoreLiteCore.longDataWordsLoopSlot slot fuel, cutoff, gtFlag,
          BytesStoreLiteCore.longDataWordsLoopStride stride fuel, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem (BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
        k' C' := by
  induction fuel generalizing idx slot stride aw τ with
  | zero =>
      simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
        BytesStoreLiteCore.longDataWordsLoopSlot,
        BytesStoreLiteCore.longDataWordsLoopStride,
        BytesStoreLiteCore.longDataWordsLoopAw,
        BytesStoreLiteCore.longDataWordsForwardFrom] using hreach
  | succ n ih =>
      have hstep := bytesStoreLiteX_setLongDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
        (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
        (payloadStart := payloadStart)
        (word := BytesStoreLiteCore.longDataWordsLoopWord mem aw ptr stride 0)
        (aw := aw)
        (awLoad := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
        hperm hreach
        (by
          simpa [BytesStoreLiteCore.longDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        (by
          intro s haw hstk
          simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
            BytesStoreLiteCore.longDataWordsLoopSlot,
            BytesStoreLiteCore.longDataWordsLoopStride,
            BytesStoreLiteCore.longDataWordsLoopAw] using
            hmloadCost 0 (Nat.zero_lt_succ n) s haw hstk)
        (by simp [BytesStoreLiteCore.longDataWordsLoopWord,
          BytesStoreLiteCore.longDataWordsLoopStride,
          BytesStoreLiteCore.longDataWordsLoopAw])
        rfl
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (BytesStoreLiteCore.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i)
              cutoff) =
              ⟨0⟩ := by
        intro i hi
        simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
          BytesStoreLiteCore.longDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hmloadCostTail : ∀ i, i < n → ∀ s : State,
          s.machineState.activeWords =
            BytesStoreLiteCore.longDataWordsLoopAw
              (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
              ptr ((⟨32⟩ : UInt256) + stride) i →
          s.machineState.stack =
            [ptr + BytesStoreLiteCore.longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i,
              BytesStoreLiteCore.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i,
              BytesStoreLiteCore.longDataWordsLoopSlot ((⟨1⟩ : UInt256) + slot) i,
              cutoff, gtFlag,
              BytesStoreLiteCore.longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i,
              len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
              ⟨263⟩, bytesStoreLiteSelWord I] →
          memoryExpansionCost s .MLOAD = mloadCost := by
        intro i hi s haw hstk
        have haw' :
            s.machineState.activeWords =
              BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride (i + 1) := by
          simpa [BytesStoreLiteCore.longDataWordsLoopAw_succ_base] using haw
        have hstk' :
            s.machineState.stack =
              [ptr + BytesStoreLiteCore.longDataWordsLoopStride stride (i + 1),
                BytesStoreLiteCore.longDataWordsLoopIndex idx (i + 1),
                BytesStoreLiteCore.longDataWordsLoopSlot slot (i + 1), cutoff, gtFlag,
                BytesStoreLiteCore.longDataWordsLoopStride stride (i + 1), len, ⟨0⟩,
                ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
                bytesStoreLiteSelWord I] := by
          simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
            BytesStoreLiteCore.longDataWordsLoopIndex_succ_base,
            BytesStoreLiteCore.longDataWordsLoopSlot_succ_base,
            BytesStoreLiteCore.longDataWordsLoopStride_succ_base,
            BytesStoreLiteCore.longDataWordsLoopStride] using hstk
        exact hmloadCost (i + 1) (Nat.succ_lt_succ hi) s haw' hstk'
      have htail := ih
        (idx := (⟨32⟩ : UInt256) + idx)
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        (aw := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (τ := sstoreAccountMap I.codeOwner τ slot
          (BytesStoreLiteCore.longDataWordsLoopWord mem aw ptr stride 0))
        hstep hcontinueTail hmloadCostTail
      simpa [BytesStoreLiteCore.longDataWordsForwardFrom,
        BytesStoreLiteCore.longDataWordsLoopIndex,
        BytesStoreLiteCore.longDataWordsLoopSlot,
        BytesStoreLiteCore.longDataWordsLoopStride,
        BytesStoreLiteCore.longDataWordsLoopAw,
        BytesStoreLiteCore.longDataWordsLoopIndex_succ_base,
        BytesStoreLiteCore.longDataWordsLoopSlot_succ_base,
        BytesStoreLiteCore.longDataWordsLoopStride_succ_base,
        BytesStoreLiteCore.longDataWordsLoopAw_succ_base,
        BytesStoreLiteCore.longDataWordsLoopWord_succ_base] using htail

theorem bytesStoreLiteX_setLongDataWordsLoopDoneNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  obtain ⟨_, _, rd2499⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have htailCond : UInt256.isZero (UInt256.lt cutoff len) ≠ ⟨0⟩ := by
    rw [hnoTail]
    decide
  have rd2531 := evm_run rd2499 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2531⟩,
    jumpiT hdoneCond (by native_decide)]
  have rd2560 := evm_run rd2531 with [
    jumpdest, pop, dup5, dup3, lt, iszero, push2 ⟨2560⟩,
    jumpiT htailCond (by native_decide)]
  have rd2571pre := evm_run rd2560 with [
    jumpdest, pop, pop, push1 ⟨1⟩, dup4, push1 ⟨1⟩, shl, add, dup5]
  obtain ⟨_, _, rd2572₀⟩ := rd2571pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2572⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2572⟩
        [gtFlag, stride, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    have hpc :
        ({ val := 2560 } + { val := 1 } + { val := 1 } + { val := 1 } +
            UInt256.ofNat 2 + { val := 1 } + UInt256.ofNat 2 + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } : UInt256) =
          ⟨2572⟩ := by native_decide
    have hshift : UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
      apply u256_inj
      unfold UInt256.shiftLeft
      rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
      show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
      rw [Nat.shiftLeft_eq]
    exact ⟨_, _, by
      simpa [hpc, hshift, sstoreAccountMap, initState, u256_add_comm len len] using rd2572₀⟩
  exact ⟨_, _, evm_run rd2572 with [
    jumpdest, pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by
      simp only [List.length_cons, List.length_nil]
      omega)]⟩

theorem bytesStoreLiteX_setLongDataWordsLoopTailLoaded
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2545⟩
        [word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awLoad rdata (cA, τ) k' C' := by
  obtain ⟨_, _, rd2499⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have rd2531 := evm_run rd2499 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2531⟩,
    jumpiT hdoneCond (by native_decide)]
  have rd2541 := evm_run rd2531 with [
    jumpdest, pop, dup5, dup3, lt, iszero, push2 ⟨2560⟩,
    jumpiNT htail]
  have rd2544pre := evm_run rd2541 with [dup7, dup5, add]
  have rd2545 := RD.mload mloadCost word awLoad rd2544pre
    (by native_decide)
    (by
      intro s haw hstk
      exact hmloadCost s haw (by simpa [u256_add_comm stride ptr] using hstk))
    (by simpa [u256_add_comm stride ptr] using hmload)
    (by simpa [u256_add_comm stride ptr] using hawLoad)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc :
      ({ val := 2531 } + { val := 1 } + { val := 1 } + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } + UInt256.ofNat 3 +
          { val := 1 } +
        { val := 1 } +
      { val := 1 } +
    { val := 1 } +
  { val := 1 } : UInt256) = ⟨2545⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2545⟩

theorem bytesStoreLiteX_setLongTailMaskShiftFromLoaded
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2545⟩
      [word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2552⟩
        [UInt256.shiftLeft len ⟨3⟩, UInt256.lnot ⟨0⟩, word, slot, cutoff,
          gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2552 := evm_run hreach with [
    push0, not, push1 ⟨3⟩, dup8, swap1, shl]
  have hpc :
      ({ val := 2545 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
          { val := 1 } + { val := 1 } + { val := 1 } : UInt256) =
        ⟨2552⟩ := by native_decide
  exact ⟨_, _, by
    simpa [hpc] using rd2552⟩

theorem bytesStoreLiteX_setLongTailMaskAnd248
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2552⟩
      [UInt256.shiftLeft len ⟨3⟩, UInt256.lnot ⟨0⟩, word, slot, cutoff,
        gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2555⟩
        [UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩), UInt256.lnot ⟨0⟩,
          word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2555 := evm_run hreach with [push1 ⟨248⟩, and]
  have hpc : ({ val := 2552 } + UInt256.ofNat 2 + { val := 1 } : UInt256) =
      ⟨2555⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2555⟩

theorem bytesStoreLiteX_setLongTailMaskShrNot
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2555⟩
      [UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩), UInt256.lnot ⟨0⟩,
        word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2557⟩
        [UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
            (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))),
          word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2557 := evm_run hreach with [shr, not]
  have hpc : ({ val := 2555 } + { val := 1 } + { val := 1 } : UInt256) =
      ⟨2557⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2557⟩

theorem bytesStoreLiteX_setLongTailMaskFinal
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word mask aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2557⟩
      [mask, word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2559⟩
        [slot, UInt256.land mask word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2559 := evm_run hreach with [and, dup2]
  have hpc : ({ val := 2557 } + { val := 1 } + { val := 1 } : UInt256) =
      ⟨2559⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2559⟩

theorem bytesStoreLiteX_setLongTailStoreFromMask
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot maskedWord cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2559⟩
      [slot, maskedWord, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2560⟩
        [slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot maskedWord) k' C' := by
  obtain ⟨_, _, rd2560₀⟩ := hreach.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc : ({ val := 2559 } + { val := 1 } : UInt256) = ⟨2560⟩ := by
    native_decide
  exact ⟨_, _, by simpa [hpc, sstoreAccountMap, initState] using rd2560₀⟩

theorem bytesStoreLiteX_setLongDataWordsLoopDoneTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (BytesStoreLiteCore.longDataTailMaskedWord word len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloaded := bytesStoreLiteX_setLongDataWordsLoopTailLoaded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (idx := idx) (slot := slot)
    (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (word := word)
    (aw := aw) (awLoad := awLoad) (mem := mem) (rdata := rdata)
    (mloadCost := mloadCost)
    hreach hdone htail hmloadCost hmload hawLoad
  obtain ⟨_, _, rd2545⟩ := hloaded
  have hshift := bytesStoreLiteX_setLongTailMaskShiftFromLoaded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2545
  obtain ⟨_, _, rd2552⟩ := hshift
  have hand := bytesStoreLiteX_setLongTailMaskAnd248
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2552
  obtain ⟨_, _, rd2555⟩ := hand
  have hmask := bytesStoreLiteX_setLongTailMaskShrNot
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2555
  obtain ⟨_, _, rd2557⟩ := hmask
  have hfinal := bytesStoreLiteX_setLongTailMaskFinal
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word)
    (mask := UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
        (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))))
    (aw := awLoad) (mem := mem) (rdata := rdata) rd2557
  obtain ⟨_, _, rd2559⟩ := hfinal
  have hstore := bytesStoreLiteX_setLongTailStoreFromMask
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot)
    (maskedWord := BytesStoreLiteCore.longDataTailMaskedWord word len)
    (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (aw := awLoad)
    (mem := mem) (rdata := rdata) hperm
    (by simpa [bytesStoreLiteOptimizedLongTailMaskedWord_eq_core] using rd2559)
  obtain ⟨_, _, rd2560⟩ := hstore
  have rd2571pre := evm_run rd2560 with [
    jumpdest, pop, pop, push1 ⟨1⟩, dup4, push1 ⟨1⟩, shl, add, dup5]
  obtain ⟨_, _, rd2572₀⟩ := rd2571pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2572⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2572⟩
        [gtFlag, stride, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (BytesStoreLiteCore.longDataTailMaskedWord word len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    have hpc :
        ({ val := 2560 } + { val := 1 } + { val := 1 } + { val := 1 } +
            UInt256.ofNat 2 + { val := 1 } + UInt256.ofNat 2 + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } : UInt256) =
          ⟨2572⟩ := by native_decide
    have hshift1 : UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
      apply u256_inj
      unfold UInt256.shiftLeft
      rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
      show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
      rw [Nat.shiftLeft_eq]
    exact ⟨_, _, by
      simpa [hpc, hshift1, sstoreAccountMap, initState, u256_add_comm len len]
        using rd2572₀⟩
  exact ⟨_, _, evm_run rd2572 with [
    jumpdest, pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by
      simp only [List.length_cons, List.length_nil]
      omega)]⟩

theorem bytesStoreLiteX_setLongDataWordsGeneratedTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw awTail wordTail : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + BytesStoreLiteCore.longDataWordsLoopStride stride i,
          BytesStoreLiteCore.longDataWordsLoopIndex idx i,
          BytesStoreLiteCore.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          BytesStoreLiteCore.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel →
      s.machineState.stack =
        [ptr + BytesStoreLiteCore.longDataWordsLoopStride stride fuel,
          BytesStoreLiteCore.longDataWordsLoopSlot slot fuel, cutoff, gtFlag,
          BytesStoreLiteCore.longDataWordsLoopStride stride fuel, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + BytesStoreLiteCore.longDataWordsLoopStride stride fuel).toNat ≥ mem.size ∨
          (ptr + BytesStoreLiteCore.longDataWordsLoopStride stride fuel) ≥
            BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding
          (ptr + BytesStoreLiteCore.longDataWordsLoopStride stride fuel).toNat 32))) =
        wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel).toNat
          (ptr + BytesStoreLiteCore.longDataWordsLoopStride stride fuel).toNat 32) = awTail)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
            (BytesStoreLiteCore.longDataWordsLoopSlot slot fuel)
            (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := bytesStoreLiteX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (aw := aw) (mem := mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := loopMloadCost)
    hperm hreach hcontinue hloopMloadCost
  exact bytesStoreLiteX_setLongDataWordsLoopDoneTail
    (σinit := σinit)
    (τ := BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := BytesStoreLiteCore.longDataWordsLoopIndex idx fuel)
    (slot := BytesStoreLiteCore.longDataWordsLoopSlot slot fuel) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := BytesStoreLiteCore.longDataWordsLoopStride stride fuel)
    (len := len) (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
    (word := wordTail) (aw := BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel)
    (awLoad := awTail) (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
    hperm hloop hdone htail hmloadCost hmload hawTail hret

theorem bytesStoreLiteX_setLongDataWordsGeneratedNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + BytesStoreLiteCore.longDataWordsLoopStride stride i,
          BytesStoreLiteCore.longDataWordsLoopIndex idx i,
          BytesStoreLiteCore.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          BytesStoreLiteCore.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem (BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := bytesStoreLiteX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (aw := aw) (mem := mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost)
    hperm hreach hcontinue hmloadCost
  exact bytesStoreLiteX_setLongDataWordsLoopDoneNoTail
    (σinit := σinit)
    (τ := BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := BytesStoreLiteCore.longDataWordsLoopIndex idx fuel)
    (slot := BytesStoreLiteCore.longDataWordsLoopSlot slot fuel) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := BytesStoreLiteCore.longDataWordsLoopStride stride fuel)
    (len := len) (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
    (aw := BytesStoreLiteCore.longDataWordsLoopAw aw ptr stride fuel)
    (mem := mem) (rdata := rdata)
    hperm hloop hdone hnoTail hret

theorem bytesStoreLiteX_setWriteLongFrom2434NoTailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (hnoTail : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i,
          BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i,
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
        (BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw aw)
            (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := bytesStoreLiteX_setLongReachLoopFrom2434
    (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact bytesStoreLiteX_setLongDataWordsGeneratedNoTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := BytesStoreLiteCore.clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (len := len) (ptr := (⟨128⟩ : UInt256))
    (ret := (⟨592⟩ : UInt256)) (payloadStart := payloadStart)
    (aw := BytesStoreLiteCore.clearCurrentHashAw aw)
    (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost)
    hperm hloopStart hcontinue hdone hnoTail hmloadCost (by native_decide)

theorem bytesStoreLiteX_setWriteLongFrom2434TailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len wordTail awTail : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (htail :
      UInt256.isZero (UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i,
          BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i,
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel,
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord fuel,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel).toNat ≥
            (BytesStoreLiteCore.clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel) ≥
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((BytesStoreLiteCore.clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel).toNat 32))) =
        wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel).toNat
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ fuel).toNat 32) =
        awTail) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
              BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (BytesStoreLiteCore.clearCurrentHashAw aw)
              (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) fuel)
            (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord fuel)
            (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := bytesStoreLiteX_setLongReachLoopFrom2434
    (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact bytesStoreLiteX_setLongDataWordsGeneratedTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := BytesStoreLiteCore.clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (len := len) (ptr := (⟨128⟩ : UInt256))
    (ret := (⟨592⟩ : UInt256)) (payloadStart := payloadStart)
    (aw := BytesStoreLiteCore.clearCurrentHashAw aw) (awTail := awTail)
    (wordTail := wordTail) (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
    (rdata := rdata) (fuel := fuel) (mloadCost := mloadCost)
    (loopMloadCost := loopMloadCost)
    hperm hloopStart hcontinue hdone htail hloopMloadCost hmloadCost hmload hawTail
    (by native_decide)

theorem bytesStoreLiteX_setWriteLongFrom2434NoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len aw : UInt256} {mem rdata : ByteArray}
    {k C mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hmloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i,
          BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i,
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom mem)
        (BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32))
        rdata
        (cA, sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw aw)
            (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact bytesStoreLiteX_setWriteLongFrom2434NoTailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    hperm hlong hreach
    (fun i hi => BytesStoreLiteCore.longDataLoopContinue len hi)
    (BytesStoreLiteCore.longDataLoopDone len)
    (BytesStoreLiteCore.longDataNoTail len hnoTailMod)
    hmloadCost

theorem bytesStoreLiteX_setWriteLongFrom2434Tail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len wordTail awTail aw : UInt256} {mem rdata : ByteArray}
    {k C mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hloopMloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i,
          BytesStoreLiteCore.longDataWordsLoopIndex ⟨0⟩ i,
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32) →
      s.machineState.stack =
        [⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32),
          BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32),
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32), len,
          ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (BytesStoreLiteCore.clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩
              (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((BytesStoreLiteCore.clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) = wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩
            (len.toNat / 32)).toNat
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32) = awTail) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
              BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (BytesStoreLiteCore.clearCurrentHashAw aw)
              (BytesStoreLiteCore.clearCurrentBaseMemFrom mem) (len.toNat / 32))
            (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact bytesStoreLiteX_setWriteLongFrom2434TailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (wordTail := wordTail) (awTail := awTail)
    (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    (loopMloadCost := loopMloadCost)
    hperm hlong hreach
    (fun i hi => BytesStoreLiteCore.longDataLoopContinue len hi)
    (BytesStoreLiteCore.longDataLoopDone len)
    (BytesStoreLiteCore.longDataTail len htailMod)
    hloopMloadCost hmloadCost hmload hawTail

theorem bytesStoreLiteX_setWriteLongFrom2434NoTailAfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat := by
    have hge := BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq :
      BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len) =
        BytesStoreLiteCore.setHelperEntryAw len :=
    BytesStoreLiteCore.clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart).size := by
    have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
      hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)) =
        BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart) :=
    BytesStoreLiteCore.clearCurrentBaseMemFrom_idem hmemGe
  obtain ⟨k', C', rd⟩ :=
    bytesStoreLiteX_setWriteLongFrom2434NoTail
      (payloadStart := payloadStart) (len := len)
      (aw := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong hnoTailMod hreach
      (by
        intro i hi s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [BytesStoreLiteCore.longDataWordsLoopAw, hcur] at hnext
        have hcurD :
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i =
              BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len)) := by
          simpa [hawEq] using hcur
        have hnextD :
            UInt256.ofNat
              (MachineState.M
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.clearCurrentHashAw
                    (BytesStoreLiteCore.setHelperEntryAw len))).toNat
                ((⟨128⟩ : UInt256) +
                  BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i).toNat 32) =
              BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len)) := by
          simpa [hawEq] using hnext
        rw [hcurD, hnextD])
  have hawLoop :
      BytesStoreLiteCore.longDataWordsLoopAw (BytesStoreLiteCore.setHelperEntryAw len)
          ⟨128⟩ ⟨32⟩ (len.toNat / 32) =
        BytesStoreLiteCore.setHelperEntryAw len := by
    simpa [hawEq] using
      BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
        (len := len) hlenMax (len.toNat / 32) (by omega)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq, hawLoop] using rd

theorem bytesStoreLiteX_setWriteLongFrom2434TailAfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len wordTail : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0)))
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
              BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
              (BytesStoreLiteCore.clearCurrentBaseMemFrom
                (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat := by
    have hge := BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq :
      BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len) =
        BytesStoreLiteCore.setHelperEntryAw len :=
    BytesStoreLiteCore.clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart).size := by
    have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
      hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)) =
        BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart) :=
    BytesStoreLiteCore.clearCurrentBaseMemFrom_idem hmemGe
  have hmloadTail :
      (if (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.clearCurrentBaseMemFrom
                (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))).size ∨
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len)))
              ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))).readWithPadding
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) =
        wordTail := by
    simpa [hmemIdem, hawEq, hwordTail] using
      BytesStoreLiteCore.longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax
  obtain ⟨k', C', rd⟩ :=
    bytesStoreLiteX_setWriteLongFrom2434Tail
      (payloadStart := payloadStart) (len := len) (wordTail := wordTail)
      (awTail := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (aw := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong htailMod hreach
      (by
        intro i hi s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [BytesStoreLiteCore.longDataWordsLoopAw, hcur] at hnext
        have hcurD :
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i =
              BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len)) := by
          simpa [hawEq] using hcur
        have hnextD :
            UInt256.ofNat
              (MachineState.M
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.clearCurrentHashAw
                    (BytesStoreLiteCore.setHelperEntryAw len))).toNat
                ((⟨128⟩ : UInt256) +
                  BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i).toNat 32) =
              BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.clearCurrentHashAw
                  (BytesStoreLiteCore.setHelperEntryAw len)) := by
          simpa [hawEq] using hnext
        rw [hcurD, hnextD])
      (by
        intro s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩
              (len.toNat / 32))
          (off := (⟨128⟩ : UInt256) +
            BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32))
          s haw hstk])
      hmloadTail
      (by
        simpa [hawEq] using
          BytesStoreLiteCore.longDataWordsLoopAw_setHelper_tail_mload_eq
            (len := len) hlenMax htailMod)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq] using rd

theorem bytesStoreLiteX_setEmptyWriteZeroFrom2434
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ ⟨0⟩) k' C' := by
  have rd2445 := evm_run hreach with [
    jumpdest, push1 ⟨32⟩, push1 ⟨31⟩, dup3, gt, push1 ⟨1⟩, dup2, eq,
    push2 ⟨2484⟩]
  have rd2449 := rd2445.jumpiNT (by native_decide)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2452 := evm_run rd2449 with [push0, dup4, iszero, push2 ⟨2461⟩]
  have rd2461 := rd2452.jumpiT (by native_decide)
    (by decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2479pre := evm_run rd2461 with [
    jumpdest, push0, not, push1 ⟨3⟩, dup6, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup5, swap1, shl, lor, dup5]
  obtain ⟨_, _, rd2480₀⟩ := rd2479pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpacked0 :
      ((⟨0⟩ : UInt256).shiftLeft ⟨1⟩).lor
          (((⟨0⟩ : UInt256).lnot.shiftRight
            ((⟨0⟩ : UInt256).shiftLeft ⟨3⟩)).lnot.land ⟨0⟩) = ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, rd2480⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2480⟩
        [(⟨0⟩ : UInt256).gt ⟨31⟩, ⟨32⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩,
          bytesStoreLiteSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, hpacked0] using rd2480₀⟩
  exact ⟨_, _, evm_run rd2480 with [
    push2 ⟨2572⟩, jump (by native_decide),
    jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setShortNonemptyWriteHeaderAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    let payloadWord : UInt256 :=
      BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.setHelperPayloadAw len)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord) k C := by
  dsimp only
  obtain ⟨_, _, rd2434⟩ := hreach
  have hnotLong : UInt256.gt len ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hshort
  have hnonzero : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by rw [hzero]; rfl)
  have hlenNotZero : UInt256.isZero len = ⟨0⟩ :=
    isZero_eq_zero_of_ne hnonzero
  have hawEntry : BytesStoreLiteCore.setHelperEntryAw len = ⟨7⟩ :=
    BytesStoreLiteCore.setHelperEntryAw_eq_7_of_short_nonzero hnz hshort
  have hawHash :
      BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len) =
        ⟨7⟩ := by
    rw [hawEntry]
    native_decide
  have hawPayload : BytesStoreLiteCore.setHelperPayloadAw len = ⟨7⟩ :=
    BytesStoreLiteCore.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have hclearSize :
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).size =
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart).size := by
    exact BytesStoreLiteCore.clearCurrentBaseMemFrom_size_of_ge32
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (by
        have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
          hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)
  have hread160 :
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).readWithPadding
          160 32 =
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart).readWithPadding 160 32 :=
    BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_read160_short_nonzero
      I.calldata len payloadStart hnz hshort hsrc
  have rd2445 := evm_run rd2434 with [
    jumpdest, push1 ⟨32⟩, push1 ⟨31⟩, dup3, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨2484⟩]
  have rd2449 := rd2445.jumpiNT (by native_decide)
    (by
      rw [hnotLong]
      decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2452 := evm_run rd2449 with [push0, dup4, iszero, push2 ⟨2461⟩]
  have rd2456 := rd2452.jumpiNT (by native_decide)
    (by simp [hlenNotZero])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2460pre := evm_run rd2456 with [pop, dup5, dup3, add]
  have haddrWord : ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ := by native_decide
  have haddr : (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 := by native_decide
  have hmload :
      (if (⟨160⟩ : UInt256).toNat ≥
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).size
          ∨ (⟨160⟩ : UInt256) ≥
              BytesStoreLiteCore.clearCurrentHashAw
                (BytesStoreLiteCore.setHelperEntryAw len) * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).readWithPadding
                (⟨160⟩ : UInt256).toNat 32))) =
        BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart := by
    rw [if_neg]
    · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hread160]
      exact (BytesStoreLiteCore.setHelperPayloadWord_eq_mload160_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc).symm
    · apply not_or.mpr
      constructor
      · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hclearSize]
        have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
          hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · rw [hawHash]
        decide
  have rd2461₀ := RD.mload
    (Cₘ (BytesStoreLiteCore.setHelperPayloadAw len) -
      Cₘ (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len)))
    (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart)
    (BytesStoreLiteCore.setHelperPayloadAw len)
    rd2460pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawHash, hawPayload]
      native_decide)
    (by
      simpa [haddrWord] using hmload)
    (by
      rw [hawHash, hawPayload, haddr]
      native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2479pre := evm_run rd2461₀ with [
    jumpdest, push0, not, push1 ⟨3⟩, dup6, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup5, swap1, shl, lor, dup5]
  obtain ⟨_, _, rd2480₀⟩ := rd2479pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [initState, BytesStoreLiteCore.setHelperPayloadWord,
      BytesStoreLiteCore.setHelperPayloadAw, List.append_assoc] using
      (evm_run rd2480₀ with [
        push2 ⟨2572⟩, jump (by native_decide),
        jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setShortNonemptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperPayloadAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have haw : BytesStoreLiteCore.setHelperPayloadAw len = ⟨7⟩ :=
    BytesStoreLiteCore.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero
      (by
        intro hzero
        apply hnz
        rw [hzero]
        decide)
      hshort
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 len (BytesStoreLiteCore.setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (BytesStoreLiteCore.setPaddedMem_mload128_short_nonzero_payloadAw
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (BytesStoreLiteCore.setHelperPayloadAw len)
      (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (BytesStoreLiteCore.setPaddedMem_mload64_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 (BytesStoreLiteCore.setShortReturnMem I.calldata len payloadStart)
      (UInt256.ofNat 7) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw, hfree]
        decide)
      (by rw [hfree]; rfl)
      (by rw [haw, hfree]; decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (UInt256.ofNat 7) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (BytesStoreLiteCore.setShortReturnMem_mload64 I.calldata len payloadStart hnz hshort hsrc)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (by
        rw [hfree, show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨192⟩) ⟨192⟩).toNat = 32 from by decide,
          BytesStoreLiteCore.setShortReturnMem_read192 I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

theorem bytesStoreLiteX_setEmptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by native_decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 BytesStoreLiteCore.setEmptyReturnMem (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      BytesStoreLiteCore.setEmptyReturnMem_mload64
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨160⟩) ⟨160⟩).toNat = 32 from by decide,
          BytesStoreLiteCore.setEmptyReturnMem_read160])
      (by evm_ov)]

theorem bytesStoreLiteX_setEmptyReturnFromWriteLongMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      BytesStoreLiteCore.clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload128
      (by native_decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      BytesStoreLiteCore.clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 BytesStoreLiteCore.setEmptyReturnMemLong (UInt256.ofNat 6)
      (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      BytesStoreLiteCore.setEmptyReturnMemLong_mload64
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨160⟩) ⟨160⟩).toNat = 32 from by decide,
          BytesStoreLiteCore.setEmptyReturnMemLong_read160])
      (by evm_ov)]

theorem bytesStoreLiteX_setLongReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have hentryGe5 : 5 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat :=
    BytesStoreLiteCore.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hentryGe1 : 1 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat := by omega
  have hawEq :
      BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len) =
        BytesStoreLiteCore.setHelperEntryAw len :=
    BytesStoreLiteCore.clearCurrentHashAw_eq_self_of_ge1 hentryGe1
  have hentryGe3 : 3 ≤ (BytesStoreLiteCore.setHelperEntryAw len).toNat := by omega
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
    have hgtNat : 31 < len.toNat := by omega
    rw [ult_one (by simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using hgtNat)]
    decide
  have hfreeGe96 : 96 ≤ (currentLengthFreePtr len).toNat :=
    BytesStoreLiteCore.currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hfreeLeMem :
      (currentLengthFreePtr len).toNat ≤
        (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).size :=
    BytesStoreLiteCore.currentLengthFreePtr_le_clearCurrentBaseMemFrom_setPaddedMem_size_u64
      I.calldata len payloadStart hnz hlenMax hsrc
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 len
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, BytesStoreLiteCore.set_activeWordsMload128_eq_self hentryGe5]
        omega)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_mload128_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact BytesStoreLiteCore.set_activeWordsMload128_eq_self hentryGe5)
      (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len)
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, BytesStoreLiteCore.activeWordsMload64_eq_self hentryGe3]
        omega)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_mload64_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact BytesStoreLiteCore.activeWordsMload64_eq_self hentryGe3)
      (by evm_ov),
    swap1, dup2]
  let returnMem := len.toByteArray.write 0
    (BytesStoreLiteCore.clearCurrentBaseMemFrom
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
    (currentLengthFreePtr len).toNat 32
  let awStore :=
    UInt256.ofNat
      (MachineState.M
        (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len)).toNat
        (currentLengthFreePtr len).toNat 32)
  have hawStore :
      UInt256.ofNat
        (MachineState.M
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len)).toNat
          (currentLengthFreePtr len).toNat 32) =
        awStore := rfl
  have rdStore := evm_run rd273 with [
    raw mstore
      (Cₘ awStore -
        Cₘ (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len)))
      returnMem awStore (by native_decide)
      (by
        intro s haw hstk
        simpa [awStore, returnMem] using
          (BytesStoreLiteCore.set_mstoreCostSpec
            (aw := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (off := currentLengthFreePtr len)
            (stk := [len, currentLengthFreePtr len, bytesStoreLiteSelWord I]) s haw hstk))
      (by rfl)
      hawStore (by evm_ov),
    push1 ⟨32⟩, add]
  have hreturnRead64 :
      returnMem.readWithPadding 64 32 = UInt256.toByteArray (currentLengthFreePtr len) := by
    simpa [returnMem] using
      BytesStoreLiteCore.currentLengthReturnWrite_preserves_read64
        (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeGe96 hfreeLeMem
        (by
          rw [BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_read64_u64
            I.calldata len payloadStart hnz hlenMax hsrc]
          exact BytesStoreLiteCore.setPaddedMem_read64 I.calldata len payloadStart hnz hsrc
            (BytesStoreLiteCore.setDataEnd_toNat_of_u64 hlenMax))
  have hreturnSize64 : 64 < returnMem.size := by
    have hge := BytesStoreLiteCore.writeWord_size_gt64_of_mem
      (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (off := (currentLengthFreePtr len).toNat) (word := len)
      (by
        rw [BytesStoreLiteCore.clearCurrentBaseMemFrom_size_of_ge32]
        · have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
            hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega
        · have hsize := BytesStoreLiteCore.setPaddedMem_size I.calldata len payloadStart
            hnz hsrc (BytesStoreLiteCore.setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega)
      hfreeLeMem
    simpa [returnMem] using hge
  have hawStoreNoWrap :
      awStore.toNat * 32 < UInt256.size := by
    simpa [awStore, hawEq] using
      BytesStoreLiteCore.setHelperEntryAw_mstoreFreePtr_mul32_lt_u64
        (len := len) hnz hlenMax
  have hawStoreGe3 : 3 ≤ awStore.toNat := by
    simpa [awStore, hawEq] using
      BytesStoreLiteCore.setHelperEntryAw_mstoreFreePtr_ge3_u64 (len := len) hnz hlenMax
  have hfinalFreePtr :
      (if (⟨64⟩ : UInt256).toNat ≥ returnMem.size
          ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (returnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        currentLengthFreePtr len := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnMem) (aw := awStore) (off := (⟨64⟩ : UInt256))
      (v := currentLengthFreePtr len)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnSize64)
      (BytesStoreLiteCore.wordMul32_not_le64_of_ge3 hawStoreGe3 hawStoreNoWrap)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let awFinal := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) = awFinal := rfl
  have hretLen : (UInt256.sub (⟨32⟩ + currentLengthFreePtr len)
      (currentLengthFreePtr len)).toNat = 32 :=
    by
      simpa [u256_add_comm (⟨32⟩ : UInt256) (currentLengthFreePtr len)] using
        BytesStoreLiteCore.currentLengthFreePtr_retLen_of_len_lt_sign_pos
          (len := len) hlenLt (Nat.pos_of_ne_zero hnz)
  have hretBytes :
      returnMem.readWithPadding (currentLengthFreePtr len).toNat
        (UInt256.sub (⟨32⟩ + currentLengthFreePtr len) (currentLengthFreePtr len)).toNat =
        UInt256.toByteArray len := by
    rw [hretLen]
    simpa [returnMem] using
      BytesStoreLiteCore.currentLengthReturnWrite_readBack
        (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeLeMem
  exact evm_run rdStore with [
    jumpdest, push1 ⟨64⟩,
    raw mload
      (Cₘ awFinal - Cₘ awStore)
      (currentLengthFreePtr len) awFinal (by native_decide)
      (by
        intro s haw hstk
        simpa [awFinal] using
          (BytesStoreLiteCore.set_mloadCostSpec
            (aw := awStore) (off := (⟨64⟩ : UInt256))
            (stk := [currentLengthFreePtr len + ⟨32⟩, bytesStoreLiteSelWord I])
            s haw
            (by
              simpa [u256_add_comm (currentLengthFreePtr len) (⟨32⟩ : UInt256)]
                using hstk)))
      hfinalFreePtr
      hawFinal (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret
      (Cₘ (UInt256.ofNat
        (MachineState.M awFinal.toNat (currentLengthFreePtr len).toNat
          (UInt256.sub (⟨32⟩ + currentLengthFreePtr len)
            (currentLengthFreePtr len)).toNat)) - Cₘ awFinal)
      (UInt256.toByteArray len) (by native_decide)
      (by
        intro s haw hstk
        simpa using
          (BytesStoreLiteCore.returnCostSpec
            (aw := awFinal) (off := currentLengthFreePtr len)
            (len := UInt256.sub (⟨32⟩ + currentLengthFreePtr len)
              (currentLengthFreePtr len))
            (stk := [bytesStoreLiteSelWord I]) s haw hstk))
      hretBytes
      (by evm_ov)]

theorem bytesStoreLiteX_setEmptyShortHeaderWriteReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (payloadStart := payloadStart) hreach
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hdecoder hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428⟩ := hdecoded
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [oldLen] using
        (evm_run rd2428 with [jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)])⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  have hwriteReach := bytesStoreLiteX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := (⟨0⟩ : UInt256)) (ret := ⟨2434⟩)
    (tail := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hcleanupReach holdNotLong (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2434⟩ := hwriteReach
  have hwrite := bytesStoreLiteX_setEmptyWriteZeroFrom2434
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (payloadStart := payloadStart)
    hperm
    rd2434
  exact bytesStoreLiteX_setEmptyReturnFromWrite
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart)
    hwrite

theorem bytesStoreLiteX_setEmptyLongHeaderWriteReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (payloadStart := payloadStart) hreach
  have hvalidHeader :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < oldLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldLen ⟨0⟩ = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := ⟨0⟩) (by
      have hpos : 0 < oldLen.toNat := by omega
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide] using hpos)
  have hshortZero : UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩ = ⟨1⟩ := by
    decide
  have hloopEntry := bytesStoreLiteX_setCurrentCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (oldLen := oldLen) (len := (⟨0⟩ : UInt256))
    (ret := ⟨2434⟩)
    (tail := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  let count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := count) (base := ⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord)
    (dead₀ := (⟨0⟩ : UInt256)) (dead₁ := oldLen) (dead₂ := (⟨0⟩ : UInt256))
    (ret := (⟨2434⟩ : UInt256))
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 6))
    (rdata := ByteArray.empty) (fuel := count.toNat)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2434⟩ := hloop
  have hwrite := bytesStoreLiteX_setEmptyWriteZeroFrom2434
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := clearDataWordsForwardFrom I.codeOwner σ
      (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩ count.toNat)
    (payloadStart := payloadStart)
    (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 6))
    (rdata := ByteArray.empty)
    hperm
    (by simpa [count] using rd2434)
  have hwrite6 : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩ count.toNat)
        ⟨0⟩ ⟨0⟩) k C := by
    simpa [BytesStoreLiteCore.clearCurrentHashAw6] using hwrite
  simpa [count] using
    bytesStoreLiteX_setEmptyReturnFromWriteLongMem
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (payloadStart := payloadStart)
      hwrite6

theorem bytesStoreLiteX_setEmptyLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem6
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setEmptyShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem6
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := BytesStoreLiteCore.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setEmptyLongMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_setEmptyLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag)
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hbad)

theorem bytesStoreLiteX_setEmptyShortMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_setEmptyShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag)
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hbad)

theorem bytesStoreLiteX_setShortNonemptyReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.setHelperPayloadAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have haw : BytesStoreLiteCore.setHelperPayloadAw len = ⟨7⟩ :=
    BytesStoreLiteCore.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero
      (by
        intro hzero
        apply hnz
        rw [hzero]
        decide)
      hshort
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 len (BytesStoreLiteCore.setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_mload128_short_nonzero_payloadAw
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (BytesStoreLiteCore.setHelperPayloadAw len)
      (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (BytesStoreLiteCore.clearCurrentBaseMemFrom_setPaddedMem_mload64_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0
      (BytesStoreLiteCore.setShortReturnMemAfterClearBase I.calldata len payloadStart)
      (UInt256.ofNat 7) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw, hfree]
        decide)
      (by rw [hfree]; rfl)
      (by rw [haw, hfree]; decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (UInt256.ofNat 7) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (BytesStoreLiteCore.setShortReturnMemAfterClearBase_mload64
        I.calldata len payloadStart hnz hshort hsrc)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (by
        rw [hfree, show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨192⟩) ⟨192⟩).toNat = 32 from by decide,
          BytesStoreLiteCore.setShortReturnMemAfterClearBase_read192
            I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

theorem bytesStoreLiteX_setShortNonemptyWriteReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    let payloadWord : UInt256 :=
      BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  have hwrite := bytesStoreLiteX_setShortNonemptyWriteHeaderAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hnz hshort hsrc
  exact bytesStoreLiteX_setShortNonemptyReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner τ ⟨0⟩
      (UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart))))
    hnz hshort hsrc hwrite

theorem bytesStoreLiteX_setWriteLongNoTailReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hwrite := bytesStoreLiteX_setWriteLongFrom2434NoTailAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
    (len := len)
    hperm hnz hlong hlenMax hsrc hnoTailMod rd2434
  exact bytesStoreLiteX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
        BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
        (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
        (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (len.toNat / 32))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreLiteX_setWriteLongTailReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hwrite := bytesStoreLiteX_setWriteLongFrom2434TailAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
    (len := len) (wordTail := wordTail)
    hperm hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail rd2434
  exact bytesStoreLiteX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreLiteX_setWriteLongNoTailReturnFromSetPadded
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  obtain ⟨k', C', rd592⟩ :=
    bytesStoreLiteX_setWriteLongFrom2434NoTail
      (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
      (len := len) (aw := BytesStoreLiteCore.setHelperEntryAw len)
      (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (rdata := ByteArray.empty)
      hperm hlong hnoTailMod rd2434
      (by
        intro i hi s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [BytesStoreLiteCore.longDataWordsLoopAw, hcur] at hnext
        rw [hcur, hnext])
  have hawLoop :
      BytesStoreLiteCore.longDataWordsLoopAw
          (BytesStoreLiteCore.clearCurrentHashAw
            (BytesStoreLiteCore.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ (len.toNat / 32) =
        BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len) :=
    BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
      (len := len) hlenMax (len.toNat / 32) (by omega)
  have hwrite : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨k', C', by simpa [hawLoop] using rd592⟩
  exact bytesStoreLiteX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
        BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
        (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
        (BytesStoreLiteCore.clearCurrentBaseMemFrom
          (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
        (len.toNat / 32))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreLiteX_setWriteLongTailReturnFromSetPadded
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (BytesStoreLiteCore.setHelperEntryAw len)
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hmloadTail :
      (if (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).size ∨
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            BytesStoreLiteCore.longDataWordsLoopAw
              (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
              ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)).readWithPadding
          (⟨128⟩ + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) =
        wordTail := by
    simpa [hwordTail] using
      BytesStoreLiteCore.longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax
  obtain ⟨k', C', rd592⟩ :=
    bytesStoreLiteX_setWriteLongFrom2434Tail
      (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
      (len := len) (wordTail := wordTail)
      (awTail := BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      (aw := BytesStoreLiteCore.setHelperEntryAw len)
      (mem := BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart)
      (rdata := ByteArray.empty)
      hperm hlong htailMod rd2434
      (by
        intro i hi s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := BytesStoreLiteCore.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [BytesStoreLiteCore.longDataWordsLoopAw, hcur] at hnext
        rw [hcur, hnext])
      (by
        intro s haw hstk
        rw [BytesStoreLiteCore.set_mloadCostSpec
          (aw := BytesStoreLiteCore.longDataWordsLoopAw
            (BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩
              (len.toNat / 32))
          (off := (⟨128⟩ : UInt256) +
            BytesStoreLiteCore.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32))
          s haw hstk])
      hmloadTail
      (BytesStoreLiteCore.longDataWordsLoopAw_setHelper_tail_mload_eq
        (len := len) hlenMax htailMod)
  have hwrite : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨k', C', rd592⟩
  exact bytesStoreLiteX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreLiteX_setLongNoTailReturnsOldShortFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreLiteX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  exact bytesStoreLiteX_setWriteLongNoTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hlong hlenMax hsrc hnoTailMod

theorem bytesStoreLiteX_setLongTailReturnsOldShortFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreLiteX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  exact bytesStoreLiteX_setWriteLongTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (wordTail := wordTail)
    hperm hbranch hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail

theorem bytesStoreLiteX_setLongNoTailReturnsOldLongNoClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreLiteX_setLongOldLongNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreLiteX_setWriteLongNoTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hlong hlenMax hsrc hnoTailMod

theorem bytesStoreLiteX_setLongTailReturnsOldLongNoClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart oldLen wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreLiteX_setLongOldLongNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreLiteX_setWriteLongTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (wordTail := wordTail)
    hperm hbranch hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail

theorem bytesStoreLiteX_setShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  have hbranch := bytesStoreLiteX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  have hwrite := bytesStoreLiteX_setShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hshort
  exact bytesStoreLiteX_setShortNonemptyReturnFromWrite
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hnz hshort hsrc hwrite

theorem bytesStoreLiteX_setDecodeShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
    let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart))
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  simpa [len, payloadStart, hlenEvm] using
    bytesStoreLiteX_setShortNonemptyReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      (len := uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
      (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      hperm hdecodedReach
      (by rw [hlenEvm]; exact hnz)
      (by rw [hlenEvm]; exact Nat.le_of_not_gt hlenMax)
      (by simpa [payloadStart, len, hlenEvm] using hsrc)
      (by simpa using hflag)
      (by simpa using hvalid)
      (by rw [hlenEvm]; exact hshort)

theorem bytesStoreLiteX_setDecodeShortNonemptyReturnsCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
    let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart))
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  exact bytesStoreLiteX_setDecodeShortNonemptyReturns
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign
    hlenMax hpayloadList hpayloadWord hnz hshort
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord] using hflag)
    (by simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord] using hvalid)

theorem bytesStoreLiteX_writeBytesHelperShortHeaderReachWriteBranch
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2599⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD slot ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C := by
  let oldLen : UInt256 :=
    UInt256.land
      (UInt256.div
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
        ⟨2⟩)
      ⟨127⟩
  have hcleanup := bytesStoreLiteX_writeBytesHelperShortHeaderReachCleanup
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata) hreach hlenMax hflag hvalid hov
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ := by
    exact currentLength_notGt31_of_lt32 holdLt32
  exact bytesStoreLiteX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldLen) (len := len)
    (ret := ⟨2643⟩) (tail := slot :: payloadStart :: len :: ret :: tail)
    (mem := mem) (aw := aw) (rdata := rdata)
    (by simpa [oldLen] using hcleanup)
    holdNotLong (by native_decide)
    (by simp only [List.length_cons]; omega)

private theorem bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hhelper := bytesStoreLiteX_pushChunkReachWriteHelperFromBody_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreLiteX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [chunksDataBase + bytesStoreLiteChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        chunksDataBase + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreLiteChunksDataBaseLiteral] using
    bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax hflag' hvalid'

theorem bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenZero : len = ⟨0⟩)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
      ((⟨0⟩ : UInt256) :: UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2643⟩ := hreach
  have hnotLong : UInt256.gt len ⟨31⟩ = ⟨0⟩ := by
    rw [hlenZero]
    native_decide
  have rd2653 := evm_run rd2643 with [
    jumpdest, push0, push1 ⟨31⟩, dup5, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨2692⟩]
  have rd2657 := rd2653.jumpiNT (by native_decide)
    (by rw [hnotLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2660 := evm_run rd2657 with [push0, dup6, iszero, push2 ⟨2669⟩]
  exact ⟨_, _, rd2660.jumpiT (by native_decide)
    (by rw [hlenZero]; decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)⟩

private theorem bytesStoreLiteX_pushChunkEmptyReachPackedHeader_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hbranch := bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreLiteX_pushChunkEmptyReachPackedHeader {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩,
        chunksDataBase + bytesStoreLiteChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        chunksDataBase + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreLiteChunksDataBaseLiteral] using
    bytesStoreLiteX_pushChunkEmptyReachPackedHeader_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag' hvalid' hlenZero

theorem bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hov : tail.length + 12 ≤ 1024) :
    let payloadWord : UInt256 :=
      uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      (UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart :: len :: ret :: tail)
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ slot storedWord) k C := by
  dsimp only
  obtain ⟨_, _, rd2643⟩ := hreach
  have hnotLong : UInt256.gt len ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hshort
  have hnonzero : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by rw [hzero]; rfl)
  have hlenNotZero : UInt256.isZero len = ⟨0⟩ :=
    isZero_eq_zero_of_ne hnonzero
  have hpayloadZeroAdd : (⟨0⟩ : UInt256) + payloadStart = payloadStart :=
    u256_zero_add payloadStart
  have rd2653 := evm_run rd2643 with [
    jumpdest, push0, push1 ⟨31⟩, dup5, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨2692⟩]
  have rd2657 := rd2653.jumpiNT (by native_decide)
    (by
      rw [hnotLong]
      decide)
    (by simp only [List.length_cons]; omega)
  have rd2660 := evm_run rd2657 with [push0, dup6, iszero, push2 ⟨2669⟩]
  have rd2664 := rd2660.jumpiNT (by native_decide)
    (by simp [hlenNotZero])
    (by simp only [List.length_cons]; omega)
  have rd2669₀ := evm_run rd2664 with [pop, dup4, dup3, add, calldataload]
  obtain ⟨_, _, rd2669⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32) ::
          UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart :: len :: ret :: tail)
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [hpayloadZeroAdd, List.append_assoc] using rd2669₀⟩
  have rd2687pre := evm_run rd2669 with [
    jumpdest, push0, not, push1 ⟨3⟩, dup8, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup7, swap1, shl, lor, dup4]
  obtain ⟨_, _, rd2688₀⟩ := rd2687pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [initState, List.append_assoc] using rd2688₀⟩

theorem bytesStoreLiteX_writeBytesNewLongReachLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlong : ¬ len.toNat < 32)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      ((⟨0⟩ : UInt256) :: bytesLikeDataBase slot ::
        UInt256.land len (UInt256.lnot ⟨31⟩) :: UInt256.gt len ⟨31⟩ ::
        (⟨0⟩ : UInt256) :: slot :: payloadStart :: len :: ret :: tail)
      (wordAt0Mem slot mem) (BytesStoreLiteCore.clearCurrentHashAw aw) rdata
      (cA, σ) k C := by
  obtain ⟨_, _, rd2643⟩ := hreach
  have hgt31 : UInt256.gt len ⟨31⟩ = ⟨1⟩ := by
    apply ugt_one
    have hge32 : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      (by omega : 31 < len.toNat)
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem slot mem).readWithPadding 0 32))) =
        bytesLikeDataBase slot := by
    rw [wordAt0Mem_read0, bytesLikeDataBase, uInt256OfByteArray_eq]
  have rd2653 := evm_run rd2643 with [
    jumpdest, push0, push1 ⟨31⟩, dup5, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨2692⟩]
  have rd2692 := rd2653.jumpiT (by native_decide)
    (by rw [hgt31]; decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [List.append_assoc] using
      (evm_run rd2692 with [
        jumpdest, push0, dup4, dup2,
        raw mstore (Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw) - Cₘ aw)
          (wordAt0Mem slot mem)
          (BytesStoreLiteCore.clearCurrentBaseAw aw) (by native_decide)
          (fun s haw hstk => by
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
              BytesStoreLiteCore.clearCurrentBaseAw])
          (by rfl) (by rfl) (by evm_ov),
        push1 ⟨32⟩, dup2,
        raw keccak256
          (Cₘ (BytesStoreLiteCore.clearCurrentHashAw aw) -
            Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw))
          (bytesLikeDataBase slot)
          (BytesStoreLiteCore.clearCurrentHashAw aw) (by native_decide)
          (fun s haw hstk => by
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
              BytesStoreLiteCore.clearCurrentHashAw, BytesStoreLiteCore.clearCurrentBaseAw])
          hslotHash (by rfl) (by evm_ov),
        push1 ⟨31⟩, not, dup8, and, swap2])⟩

theorem bytesStoreLiteX_writeBytesNewLongDataWordsLoopStep
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx cutoff) = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
        (((⟨32⟩ : UInt256) + idx) :: ((⟨1⟩ : UInt256) + slot) :: cutoff ::
          gtFlag :: ((⟨32⟩ : UInt256) + stride) :: baseSlot :: payloadStart :: len ::
          ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0)) k' C' := by
  obtain ⟨_, _, rd2707⟩ := hreach
  have rd2716 := evm_run rd2707 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2739⟩,
    jumpiNT hcontinue]
  have rd2721pre := evm_run rd2716 with [dup7, dup6, add, calldataload, dup3]
  obtain ⟨_, _, rd2722₀⟩ := rd2721pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2722⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2722⟩
        (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
          ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0)) k C := by
    have hpc :
        ({ val := 2707 } + { val := 1 } + { val := 1 } + { val := 1 } +
              { val := 1 } + { val := 1 } + UInt256.ofNat 3 + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } : UInt256) = ⟨2722⟩ := by
      native_decide
    exact ⟨_, _, by
      simpa [hpc, bytesStoreLiteCalldataLongDataWord,
        BytesStoreLiteCore.longDataWordsLoopStride, u256_add_comm payloadStart stride,
        sstoreAccountMap, initState] using rd2722₀⟩
  exact ⟨_, _, by
    simpa [u256_add_comm idx ⟨32⟩, u256_add_comm slot ⟨1⟩,
      u256_add_comm stride ⟨32⟩, List.append_assoc] using
      (evm_run rd2722 with [
        push1 ⟨32⟩, swap5, dup6, add, swap5, push1 ⟨1⟩, swap1,
        swap3, add, swap2, add, push2 ⟨2707⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_writeBytesNewLongDataWordsLoopGenerated
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
        (BytesStoreLiteCore.longDataWordsLoopIndex idx fuel ::
          BytesStoreLiteCore.longDataWordsLoopSlot slot fuel :: cutoff :: gtFlag ::
          BytesStoreLiteCore.longDataWordsLoopStride stride fuel :: baseSlot ::
          payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA,
          bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner τ slot payloadStart stride I fuel)
        k' C' := by
  induction fuel generalizing idx slot stride τ with
  | zero =>
      simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
        BytesStoreLiteCore.longDataWordsLoopSlot,
        BytesStoreLiteCore.longDataWordsLoopStride,
        bytesStoreLiteCalldataLongDataForwardFrom] using hreach
  | succ n ih =>
      have hstep := bytesStoreLiteX_writeBytesNewLongDataWordsLoopStep
        (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (τ := τ) (idx := idx) (slot := slot)
        (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride)
        (baseSlot := baseSlot) (payloadStart := payloadStart) (len := len)
        (ret := ret) (tail := tail) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by
          simpa [BytesStoreLiteCore.longDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (BytesStoreLiteCore.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i)
              cutoff) =
              ⟨0⟩ := by
        intro i hi
        simpa [BytesStoreLiteCore.longDataWordsLoopIndex,
          BytesStoreLiteCore.longDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have htail := ih
        (idx := (⟨32⟩ : UInt256) + idx)
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        (τ := sstoreAccountMap I.codeOwner τ slot
          (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0))
        hstep hcontinueTail
      simpa [bytesStoreLiteCalldataLongDataForwardFrom,
        BytesStoreLiteCore.longDataWordsLoopIndex,
        BytesStoreLiteCore.longDataWordsLoopSlot,
        BytesStoreLiteCore.longDataWordsLoopStride,
        BytesStoreLiteCore.longDataWordsLoopIndex_succ_base,
        BytesStoreLiteCore.longDataWordsLoopSlot_succ_base,
        BytesStoreLiteCore.longDataWordsLoopStride_succ_base,
        bytesStoreLiteCalldataLongDataWord_succ_base] using htail

theorem bytesStoreLiteX_writeBytesNewLongDataWordsLoopDoneNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret tail mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ baseSlot
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  obtain ⟨_, _, rd2707⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have htailCond : UInt256.isZero (UInt256.lt cutoff len) ≠ ⟨0⟩ := by
    rw [hnoTail]
    decide
  have rd2739 := evm_run rd2707 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2739⟩,
    jumpiT hdoneCond (by native_decide)]
  have rd2767 := evm_run rd2739 with [
    jumpdest, pop, dup7, dup3, lt, iszero, push2 ⟨2767⟩,
    jumpiT htailCond (by native_decide)]
  have rd2779pre := evm_run rd2767 with [
    jumpdest, pop, pop, push1 ⟨1⟩, dup6, push1 ⟨1⟩, shl, add, dup4]
  obtain ⟨_, _, rd2779₀⟩ := rd2779pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2779⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2779⟩
        (gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ baseSlot
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    have hpc :
        ({ val := 2767 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
            { val := 1 } + UInt256.ofNat 2 + { val := 1 } + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } : UInt256) = ⟨2779⟩ := by
      native_decide
    have hshift1 : UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
      apply u256_inj
      unfold UInt256.shiftLeft
      rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
      show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
      rw [Nat.shiftLeft_eq]
    exact ⟨_, _, by
      simpa [hpc, hshift1, sstoreAccountMap, initState, u256_add_comm len len]
        using rd2779₀⟩
  exact ⟨_, _, evm_run rd2779 with [
    pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by omega)]⟩

theorem bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, τ) k C)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret tail
        (wordAt0Mem slot mem) (BytesStoreLiteCore.clearCurrentHashAw aw) rdata
        (cA, sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner τ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopEntry := bytesStoreLiteX_writeBytesNewLongReachLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata)
    hreach hlong (by omega)
  have hloop := bytesStoreLiteX_writeBytesNewLongDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := bytesLikeDataBase slot)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨0⟩ : UInt256)) (baseSlot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw aw) (rdata := rdata)
    (fuel := len.toNat / 32)
    hperm hloopEntry
    (fun i hi => BytesStoreLiteCore.longDataLoopContinue len hi)
    hov
  exact bytesStoreLiteX_writeBytesNewLongDataWordsLoopDoneNoTail
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner τ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
    (idx := BytesStoreLiteCore.longDataWordsLoopIndex (⟨0⟩ : UInt256) (len.toNat / 32))
    (slot := BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
    (baseSlot := slot) (payloadStart := payloadStart) (len := len) (ret := ret)
    (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw aw) (rdata := rdata)
    hperm hloop
    (BytesStoreLiteCore.longDataLoopDone len)
    (BytesStoreLiteCore.longDataNoTail len hnoTailMod)
    hret hov

private theorem bytesStoreLiteX_pushChunkShortNonemptyWriteHeaderFromBody_literal {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreLiteChunksLengthWord σ I)
        storedWord) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreLiteChunksLengthWord σ I, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreLiteX_pushChunkShortNonemptyWriteHeaderFromBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, chunksDataBase + bytesStoreLiteChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩, chunksDataBase + bytesStoreLiteChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I)
        storedWord) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreLiteChunksDataBaseLiteral] using
    bytesStoreLiteX_pushChunkShortNonemptyWriteHeaderFromBody_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag' hvalid' hnz hshort

theorem bytesStoreLiteX_pushChunkEmptyWriteHeader {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot payloadStart len sel : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k C := by
  obtain ⟨_, _, rd2669⟩ := hreach
  have rd2687pre := evm_run rd2669 with [
    jumpdest, push0, not, push1 ⟨3⟩, dup8, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup7, swap1, shl, lor, dup4]
  obtain ⟨_, _, rd2688₀⟩ := rd2687pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [initState, hlenZero] using rd2688₀⟩

theorem bytesStoreLiteX_pushChunkEmptyWriteHeaderFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, chunksDataBase + bytesStoreLiteChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩, chunksDataBase + bytesStoreLiteChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩) k C := by
  have hpacked := bytesStoreLiteX_pushChunkEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hlenZero
  exact bytesStoreLiteX_pushChunkEmptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreLiteSelWord I)
    hperm hpacked hlenZero

theorem bytesStoreLiteX_pushChunkReturnFromEmptyWrite {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len sel : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)), sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2688⟩ := hreach
  have rd2572 := evm_run rd2688 with [push2 ⟨2572⟩, jump (by native_decide)]
  have rd1617 := evm_run rd2572 with [
    jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)]
  have rd1622pre := evm_run rd1617 with [jumpdest, pop, pop, push1 ⟨1⟩]
  obtain ⟨_, _, rd1623₀⟩ := rd1622pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1623⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1623⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
          len, payloadStart, ⟨263⟩, sel]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1623₀⟩
  exact ⟨_, _, evm_run rd1623 with [
    swap3, swap2, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreLiteX_pushChunkEmptyReachReturnWord {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [((sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩).find? I.codeOwner |>.option
            ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩) k C := by
  have hwrite := bytesStoreLiteX_pushChunkEmptyWriteHeaderFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hlenZero
  exact bytesStoreLiteX_pushChunkReturnFromEmptyWrite
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreLiteSelWord I) hwrite

theorem bytesStoreLiteX_pushChunkShortNonemptyReachReturnWord {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) storedWord
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ') k C := by
  dsimp only
  have hwrite := bytesStoreLiteX_pushChunkShortNonemptyWriteHeaderFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hnz hshort
  exact bytesStoreLiteX_pushChunkReturnFromEmptyWrite
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I)
      (UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreLiteChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreLiteSelWord I)
    hwrite

theorem bytesStoreLiteX_pushChunkShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (bytesStoreLiteX_pushChunkShortNonemptyReachReturnWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag hvalid hnz hshort)

theorem bytesStoreLiteX_pushChunkEmptyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (bytesStoreLiteX_pushChunkEmptyReachReturnWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag hvalid hlenZero)

theorem bytesStoreLiteMappedLengthSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
      bytesStoreLiteMappedLengthSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem_size]
  unfold bytesStoreLiteMappedLengthSlot mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩

theorem bytesStoreLiteChunkLengthSlotHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase]
    using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreLiteX_mappedLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteMappedLengthHeaderWord σ I, ⟨1137⟩,
        bytesStoreLiteMappedLengthSlot I, ⟨0⟩, bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1113⟩ := hreach
  have hslot := bytesStoreLiteMappedLengthSlotHash I
  have rd1127 := evm_run rd1113 with [
    jumpdest, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteMappedLengthKeyWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (bytesStoreLiteMappedLengthSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1128₀⟩ := rd1127.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1128⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1129⟩
        [bytesStoreLiteMappedLengthHeaderWord σ I, bytesStoreLiteMappedLengthSlot I, ⟨0⟩,
          bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteMappedLengthHeaderWord, initState] using rd1128₀⟩
  exact ⟨_, _, evm_run rd1128 with [
    push2 ⟨1137⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_chunkLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteChunkLengthHeaderWord σ I, ⟨1137⟩,
        bytesStoreLiteChunkLengthSlot I, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1693⟩ := hreach
  have hslot := bytesStoreLiteChunkLengthSlotHash
  have rd1699 := evm_run rd1693 with [
    jumpdest, push0, push1 ⟨1⟩, dup3, dup2]
  obtain ⟨_, _, rd1700₀⟩ := rd1699.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1700⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
        [bytesStoreLiteChunksLengthWord σ I, bytesStoreLiteChunkLengthIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1700₀⟩
  have hlt : UInt256.lt (bytesStoreLiteChunkLengthIndexWord I)
      (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1713 := evm_run rd1700 with [
    dup2, lt, push2 ⟨1713⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1722 := evm_run rd1713 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    add, dup1]
  obtain ⟨_, _, rd1723₀⟩ := rd1722.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1723⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
        [bytesStoreLiteChunkLengthHeaderWord σ I, bytesStoreLiteChunkLengthSlot I, ⟨0⟩,
          bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunkLengthHeaderWord, bytesStoreLiteChunkLengthSlot, initState]
        using rd1723₀⟩
  exact ⟨_, _, evm_run rd1723 with [
    push2 ⟨1137⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_chunkLengthOob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1693⟩ := hreach
  have rd1699 := evm_run rd1693 with [
    jumpdest, push0, push1 ⟨1⟩, dup3, dup2]
  obtain ⟨_, _, rd1700₀⟩ := rd1699.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1700⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
        [bytesStoreLiteChunksLengthWord σ I, bytesStoreLiteChunkLengthIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1700₀⟩
  have hlt : UInt256.lt (bytesStoreLiteChunkLengthIndexWord I)
      (bytesStoreLiteChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1700 with [
    dup2, lt, push2 ⟨1713⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1713⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_chunkLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩,
        bytesStoreLiteChunkLengthSlot I, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (bytesStoreLiteX_chunkLengthReachDecoder hreach hbound) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_chunkLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        bytesStoreLiteChunkLengthSlot I, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (bytesStoreLiteX_chunkLengthReachDecoder hreach hbound) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_chunkLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [len, bytesStoreLiteChunkLengthSlot I, ⟨0⟩, bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1137⟩ := hdecoded
  have rd263 := evm_run rd1137 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact bytesStoreLiteX_returnWord263OfMem
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    ⟨_, _, rd263⟩

theorem bytesStoreLiteX_chunkLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreLiteX_chunkLengthReturnFromDecoded
    (bytesStoreLiteX_chunkLengthDecoderLongValid hreach hbound hflag hvalid)

theorem bytesStoreLiteX_chunkLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreLiteX_chunkLengthReturnFromDecoded
    (bytesStoreLiteX_chunkLengthDecoderShortValid hreach hbound hflag hvalid)

theorem bytesStoreLiteX_chunkLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (bytesStoreLiteX_chunkLengthReachDecoder hreach hbound) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_chunkLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreLiteChunkLengthIndexWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (bytesStoreLiteX_chunkLengthReachDecoder hreach hbound) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_mappedLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩,
        bytesStoreLiteMappedLengthSlot I, ⟨0⟩, bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (bytesStoreLiteX_mappedLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_mappedLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        bytesStoreLiteMappedLengthSlot I, ⟨0⟩, bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (bytesStoreLiteX_mappedLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_mappedLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [len, bytesStoreLiteMappedLengthSlot I, ⟨0⟩, bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1137⟩ := hdecoded
  have rd263 := evm_run rd1137 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact bytesStoreLiteX_returnWord263OfMem
    (mem := twoWordHashMem (bytesStoreLiteMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
    (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size])
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
    ⟨_, _, rd263⟩

theorem bytesStoreLiteX_mappedLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreLiteX_mappedLengthReturnFromDecoded
    (bytesStoreLiteX_mappedLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreLiteX_mappedLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreLiteX_mappedLengthReturnFromDecoded
    (bytesStoreLiteX_mappedLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreLiteX_mappedLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (bytesStoreLiteX_mappedLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_mappedLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreLiteMappedLengthKeyWord I, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (bytesStoreLiteX_mappedLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteSetSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteSetByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x1c, 0x52, 0x47, 0x7d]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteSetPacketByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x0a, 0xb2, 0x59, 0x00]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLitePacketTagSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x99, 0x3e, 0x0a, 0x90]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteCurrentLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteClearCurrentSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLitePushChunkSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLitePacketLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteMappedLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x39, 0x1d, 0x72, 0x80]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteChunkLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteDecode_packetTag {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (packetTagGetter.params.map Param.name)
      (transitionSignature packetTagGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreLiteDecode_currentLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (currentLengthGetter.params.map Param.name)
      (transitionSignature currentLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreLiteDecode_clearCurrent {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (clearCurrentTransition.params.map Param.name)
      (transitionSignature clearCurrentTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreLiteDecode_setByte {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetByteLocals I) := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = _
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreLiteSetByteIndexWord,
    bytesStoreLiteSetByteValueWord, bytesStoreLiteSetByteLocals]
    using decodeCalldata_uint256_uint8_ok (cd := I.calldata) (x := "index") (y := "value")
      hsz68 hhi hcanon

theorem bytesStoreLiteDecode_setByte_none_noncanon_value {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreLiteSetByteValueWord]
    using decodeCalldata_uint256_uint8_none_noncanon1 (cd := I.calldata) (x := "index")
      (y := "value") hsz68 hhi hnc

theorem bytesStoreLiteDecode_setByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_short (cd := I.calldata) (x := "index")
      (y := "value") hshort

theorem bytesStoreLiteDecode_setByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_huge (cd := I.calldata) (x := "index")
      (y := "value") hbig

theorem bytesStoreLiteDecode_setPacketByte {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata =
        some (((∅ : Store).insert "byteIndex"
          (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat))).insert "value"
          (.int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat))) := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = _
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreLiteSetByteIndexWord,
    bytesStoreLiteSetByteValueWord]
    using decodeCalldata_uint256_uint8_ok (cd := I.calldata) (x := "byteIndex") (y := "value")
      hsz68 hhi hcanon

theorem bytesStoreLiteDecode_setPacketByte_none_noncanon_value {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreLiteSetByteValueWord]
    using decodeCalldata_uint256_uint8_none_noncanon1 (cd := I.calldata) (x := "byteIndex")
      (y := "value") hsz68 hhi hnc

theorem bytesStoreLiteDecode_setPacketByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_short (cd := I.calldata) (x := "byteIndex")
      (y := "value") hshort

theorem bytesStoreLiteDecode_setPacketByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_huge (cd := I.calldata) (x := "byteIndex")
      (y := "value") hbig

theorem bytesStoreLiteDecode_packetLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (packetLengthGetter.params.map Param.name)
      (transitionSignature packetLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreLiteDecode_mappedLength {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata =
        some ((∅ : Store).insert "key"
          (.int (Int.ofNat (bytesStoreLiteMappedLengthKeyWord I).toNat))) := by
  show decodeCalldata ["key"] [uint256] I.calldata = _
  simpa [uint256, abiUInt256, bytesStoreLiteMappedLengthKeyWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "key") hsz36 hhi

theorem bytesStoreLiteDecode_mappedLength_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["key"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "key") hshort

theorem bytesStoreLiteDecode_mappedLength_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["key"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "key") hbig

theorem bytesStoreLiteDecode_chunkLength {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata =
        some (bytesStoreLiteChunkLengthLocals I) := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = _
  simpa [uint256, abiUInt256, bytesStoreLiteChunkLengthIndexWord,
    bytesStoreLiteChunkLengthLocals]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "chunkIndex") hsz36 hhi

theorem bytesStoreLiteDecode_chunkLength_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "chunkIndex") hshort

theorem bytesStoreLiteDecode_chunkLength_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "chunkIndex") hbig

theorem bytesStoreLiteDecode_pushChunk_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  unfold decodeCalldata
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hnotDyn :
        ¬ ([ABIType.bytes].any isDynamicABIType = true ∧ 2 ^ 255 ≤ I.calldata.toList.length) := by
      intro h
      rw [htlen] at h
      omega
    rw [if_neg hnotDyn]
    have hnotArgsHuge :
        ¬ ([ABIType.bytes].isEmpty = false ∧
            2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
      intro h
      rw [List.length_drop, htlen] at h
      omega
    rw [if_neg hnotArgsHuge]
    have hnotTotal :
        ¬ (solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧
            2 ^ 255 ≤ I.calldata.toList.length) := by
      intro h
      rw [htlen] at h
      omega
    rw [if_neg hnotTotal]
    have hhead : (I.calldata.toList.drop 4).length < 32 := by
      rw [List.length_drop, htlen]
      omega
    have hhead' : I.calldata.toList.length - 4 < 32 := by
      rw [htlen]
      omega
    simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType, hhead']

theorem bytesStoreLiteDecode_pushChunk_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_huge (x := "value") hbig

theorem bytesStoreLiteDecode_pushChunk_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_offset_huge (x := "value") hsz36 hoff

theorem bytesStoreLiteDecode_pushChunk_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_short (x := "value") hsz36 hhi hshort

theorem bytesStoreLiteDecode_pushChunk_none_lengthHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_huge (x := "value") hsz36 hhi hoffMax hlenWord
    hlenHuge

theorem bytesStoreLiteDecode_pushChunk_none_payloadShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_payload_short (x := "value") hsz36 hhi hoffMax hlenWord
    hlenMax hpayload

theorem bytesStoreLiteDecode_pushChunk {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.bytes (BytesStoreLiteCore.setDecodedValueBytes I))) := by
  show decodeCalldata ["value"] [.bytes] I.calldata =
      some ((∅ : Store).insert "value" (.bytes (BytesStoreLiteCore.setDecodedValueBytes I)))
  simpa [BytesStoreLiteCore.setDecodedValueBytes] using
    decodeCalldata_bytes_some (cd := I.calldata) (x := "value")
      hsz36 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreLiteDecode_pushChunk_empty {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.bytes ByteArray.empty)) := by
  show decodeCalldata ["value"] [.bytes] I.calldata =
    some ((∅ : Store).insert "value" (.bytes ByteArray.empty))
  have hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    rw [hlenZero]
    norm_num [ABI.solcMaxU64]
  have hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) := by
    rw [hlenZero]
    rfl
  have hdec := decodeCalldata_bytes_some (cd := I.calldata) (x := "value")
    hsz36 hsizeSign hoffMax hlenWord hlenMax hpayload
  simpa [hlenZero] using hdec

theorem bytesStoreLiteChunkLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteChunkLengthLocals I) := by
    exact bytesStoreLiteDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteChunkLengthSlot I) =
          bytesStoreLiteChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreLiteChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthRef I) =
          .ok (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteChunkLengthSlot I)
      (header := bytesStoreLiteChunkLengthHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreLiteChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreLiteChunkLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreLiteX_chunkLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hbound hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreLiteChunkLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteChunkLengthLocals I) := by
    exact bytesStoreLiteDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteChunkLengthSlot I) =
          bytesStoreLiteChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreLiteChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalidSolm :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteChunkLengthSlot I)
      (header := bytesStoreLiteChunkLengthHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStoreLiteChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteChunkLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.land
              (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreLiteChunkLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreLiteX_chunkLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hbound hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreLiteChunkLengthOobRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteChunkLengthLocals I) := by
    exact bytesStoreLiteDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      ¬ (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreLiteChunkLengthBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm
  exact (bytesStoreLiteX_chunkLengthOob
      (g := Sat256.ofUInt256 g) hreach hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteChunkLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteChunkLengthLocals I) := by
    exact bytesStoreLiteDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteChunkLengthSlot I) =
          bytesStoreLiteChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreLiteChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthRef I) = .revert := by
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteChunkLengthSlot I)
      (header := bytesStoreLiteChunkLengthHeaderWord σ_evm I)
      (bytesStoreLiteChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreLiteChunkLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreLiteX_chunkLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hbound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteChunkLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteChunkLengthLocals I) := by
    exact bytesStoreLiteDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteChunkLengthSlot I) =
          bytesStoreLiteChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreLiteChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbadSolm :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthRef I) = .revert := by
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteChunkLengthSlot I)
      (header := bytesStoreLiteChunkLengthHeaderWord σ_evm I)
      (bytesStoreLiteChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbadSolm])
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreLiteChunkLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreLiteX_chunkLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hbound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteChunkLengthRuntimeDecoded {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreLiteChunkLengthIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat
  · by_cases hflag : UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid : UInt256.sub
          (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteChunkLengthShortValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hvalid
      · have hbad : UInt256.sub
            (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
          not_ne_iff.mp hvalid
        exact bytesStoreLiteChunkLengthShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hbad
    · by_cases hvalid : UInt256.sub
          (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteChunkLengthLongValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hvalid
      · have hbad : UInt256.sub
            (UInt256.land (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (bytesStoreLiteChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
          not_ne_iff.mp hvalid
        exact bytesStoreLiteChunkLengthLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hbad
  · exact bytesStoreLiteChunkLengthOobRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound

theorem bytesStoreLiteChunkLengthDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreach := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_chunkLength_none_short (I := I) hshort
  exact (bytesStoreLiteX_chunkLengthDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteChunkLengthDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteChunkLengthSelector_size hsel
  have hreach := bytesStoreLiteReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_chunkLength_none_huge (I := I) hbig
  exact (bytesStoreLiteX_chunkLengthDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteChunkLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 36
  · exact bytesStoreLiteChunkLengthDecodeShortRuntime hcode hsize hperm hwv hsel hshort
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact bytesStoreLiteChunkLengthRuntimeDecoded
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact bytesStoreLiteChunkLengthDecodeHugeRuntime hcode hsize hperm hwv hsel hbig

theorem bytesStoreLiteMappedLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteMappedLengthLocals I) := by
    simpa [bytesStoreLiteMappedLengthLocals] using bytesStoreLiteDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
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
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreLiteMappedLengthKeyWord I).toNat))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreLiteMappedLengthSlot] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthRef I) =
          .ok (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteMappedLengthSlot I)
      (header := bytesStoreLiteMappedLengthHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreLiteMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreLiteMappedLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_mappedLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreLiteMappedLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteMappedLengthLocals I) := by
    simpa [bytesStoreLiteMappedLengthLocals] using bytesStoreLiteDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
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
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreLiteMappedLengthKeyWord I).toNat))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreLiteMappedLengthSlot] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLiteMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteMappedLengthSlot I)
      (header := bytesStoreLiteMappedLengthHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStoreLiteMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteMappedLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat
              (UInt256.land
                (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreLiteMappedLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_mappedLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land
            (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreLiteMappedLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteMappedLengthLocals I) := by
    simpa [bytesStoreLiteMappedLengthLocals] using bytesStoreLiteDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreLiteMappedLengthSlot] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthRef I) = .revert := by
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteMappedLengthSlot I)
      (header := bytesStoreLiteMappedLengthHeaderWord σ_evm I)
      (bytesStoreLiteMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body .reverted := by
    exact bytesStoreLiteMappedLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_mappedLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteMappedLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreachSel := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreLiteX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreLiteMappedLengthLocals I) := by
    simpa [bytesStoreLiteMappedLengthLocals] using bytesStoreLiteDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteMappedLengthSlot I) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreLiteMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreLiteMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreLiteMappedLengthSlot] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthRef I) = .revert := by
    exact bytesStoreLiteReadLengthRevertOfHeaderLoad
      (er := bytesStoreLiteMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreLiteMappedLengthSlot I)
      (header := bytesStoreLiteMappedLengthHeaderWord σ_evm I)
      (bytesStoreLiteMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteMappedLengthLocals I) mappedLengthGetter.body .reverted := by
    exact bytesStoreLiteMappedLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_mappedLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteMappedLengthRuntimeDecoded {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteMappedLengthShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteMappedLengthShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hbad
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteMappedLengthLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteMappedLengthLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hbad

theorem bytesStoreLiteMappedLengthDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreach := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_mappedLength_none_short (I := I) hshort
  exact (bytesStoreLiteX_mappedLengthDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteMappedLengthDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteMappedLengthSelector_size hsel
  have hreach := bytesStoreLiteReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_mappedLength_none_huge (I := I) hbig
  exact (bytesStoreLiteX_mappedLengthDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_short (I := I) hshort
  exact (bytesStoreLiteX_pushChunkDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_huge (I := I) hbig
  exact (bytesStoreLiteX_pushChunkDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_offsetHuge (I := I) hsz36 hoff
  exact (bytesStoreLiteX_pushChunkDecodeOffsetHuge
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_lengthShort (I := I) hsz36 hhi hlenShort
  exact (bytesStoreLiteX_pushChunkDecodeLengthShort
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax hlenShort)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_lengthHuge (I := I)
    hsz36 hhi hoffMax hlenWord hlenHuge
  exact (bytesStoreLiteX_pushChunkDecodeLengthHuge
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk_none_payloadShort (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreLiteX_pushChunkDecodePayloadShort
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
      hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkEmptyRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hzero :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
        (oldLen + ⟨1⟩))
      evmSolm0.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
      (chunksDataBase + oldLen) ⟨0⟩
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := bytesStoreLiteDecode_pushChunk_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    rw [hlenZero]
    apply ugt_zero
    rw [u256_add_assoc]
    rw [show ((⟨0⟩ : UInt256) + ⟨32⟩) = ⟨32⟩ by native_decide]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkEmptyReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
        (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        hperm hdecodedReach hlenMaxWord
        (bytesStoreLitePushChunkEmptyFlagOfZero_of_ne (σ := σ_evm) (I := I)
          (by simpa [oldLen] using hne) (by simpa [oldLen] using hzero))
        (bytesStoreLitePushChunkEmptyValidOfZero_of_ne (σ := σ_evm) (I := I)
          (by simpa [oldLen] using hne) (by simpa [oldLen] using hzero))
        hlenZero
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + oldLen) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
      simpa [evmSolm0, oldLen, bytesStoreLitePushChunkSlot] using
        bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts
    exact hload.trans (by
      simpa [oldLen, bytesStoreLitePushChunkHeaderWord, bytesStoreLitePushChunkSlot] using hzero)
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evmSolm0 chunksRef (some (.bytes ByteArray.empty)) = .ok evmSolm1 := by
    simpa [evmSolm1] using
      bytesStoreLitePushChunkEmptyPushArray_of_ne (evm := evmSolm0) oldLen
        (by simpa [oldLen] using hne) hloadLen hloadElem
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkEmptyBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have hpostAccounts :
      accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    simpa [finalEvmMap, evmSolm1, evmSolm0] using
      accountMapEquiv_storageStore_initState_codeOwner_two
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        ⟨1⟩ (oldLen + ⟨1⟩) (chunksDataBase + oldLen) ⟨0⟩
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

theorem bytesStoreLitePushChunkEmptyShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.land (UInt256.div oldHeader ⟨2⟩) ⟨127⟩
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
        (oldLen + ⟨1⟩))
      evmSolm0.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
      (chunksDataBase + oldLen) ⟨0⟩
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := bytesStoreLiteDecode_pushChunk_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    rw [hlenZero]
    apply ugt_zero
    rw [u256_add_assoc]
    rw [show ((⟨0⟩ : UInt256) + ⟨32⟩) = ⟨32⟩ by native_decide]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using congrArg (fun w => UInt256.land w ⟨1⟩) hheaderAfter |>.trans hflag
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkEmptyReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
        (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        hperm hdecodedReach hlenMaxWord hflagAfter hvalidAfter hlenZero
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evmSolm0 chunksRef (some (.bytes ByteArray.empty)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen] using
      bytesStoreLitePushChunkEmptyPushArrayShortPacked_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkEmptyBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have hpostAccounts :
      accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    simpa [finalEvmMap, evmSolm1, evmSolm0] using
      accountMapEquiv_storageStore_initState_codeOwner_two
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        ⟨1⟩ (oldLen + ⟨1⟩) (chunksDataBase + oldLen) ⟨0⟩
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

theorem bytesStoreLitePushChunkEmptyShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkEmptyShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hflag hvalid

set_option maxHeartbeats 4000000 in
theorem bytesStoreLitePushChunkShortNonemptyShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.land (UInt256.div oldHeader ⟨2⟩) ⟨127⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let storedWord : UInt256 :=
    bytesStoreLiteOptimizedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
        (oldLen + ⟨1⟩))
      evmSolm0.executionEnv.codeOwner (chunksDataBase + oldLen)
      (solidityShortBytesWord value)
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
      (chunksDataBase + oldLen) storedWord
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hsrcConcrete :
      (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩).toNat +
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        I.calldata.size := by
    simpa [payloadStart, len] using hsrc
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hstoredDirect :
      bytesStoreLiteOptimizedShortStoredWord I len payloadStart =
        solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I) := by
    exact bytesStoreLiteOptimizedShortStoredWord_abbrev_eq_solidityShortBytesWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbiLocal hpayloadStartLocal hoffMax
      (by simpa [len] using hnz)
      (by simpa [len] using hshort)
      hsrc hpayloadList
  have hstoredEq : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using hstoredDirect
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap, storedWord, len, payloadStart, hlenEvm] using
      bytesStoreLiteX_pushChunkShortNonemptyReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
        (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        hperm hdecodedReach hlenMaxWord hflagAfter hvalidAfter
        (by rw [hlenEvm]; exact hnz)
        (by rw [hlenEvm]; exact hshort)
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    exact hshort
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen] using
      bytesStoreLitePushChunkShortPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSize hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have hpostAccounts :
      accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    simpa [finalEvmMap, evmSolm1, evmSolm0, hstoredEq] using
      accountMapEquiv_storageStore_initState_codeOwner_two
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        ⟨1⟩ (oldLen + ⟨1⟩) (chunksDataBase + oldLen) (solidityShortBytesWord value)
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 4000000 in
theorem bytesStoreLitePushChunkShortNonemptyShortPackedRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkShortNonemptyShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hshort hflag hvalid

theorem bytesStoreLitePushChunkLongMalformedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩) ⟨32⟩) =
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hbadAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hbad)
  have hrev := bytesStoreLiteX_pushChunkLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    (len := uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
    (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    hperm hdecodedReach hlenMaxWord hflagAfter hbadAfter
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .revert := by
    exact bytesStoreLitePushChunkMalformedLongPushArray_of_post_header (evm := evmSolm0)
      oldLen oldHeader value hloadLen
      (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
      (by simpa [oldHeader] using hflag)
      (by simpa [oldHeader] using hbad)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
    exact bytesStoreLitePushChunkBodyRevertsOfPush (evm := evmSolm0) (value := value)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLitePushChunkLongMalformedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongMalformedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hflag hbad

theorem bytesStoreLitePushChunkShortMalformedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hbadAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hbad)
  have hrev := bytesStoreLiteX_pushChunkShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    (len := uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
    (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    hperm hdecodedReach hlenMaxWord hflagAfter hbadAfter
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .revert := by
    exact bytesStoreLitePushChunkMalformedShortPushArray_of_post_header (evm := evmSolm0)
      oldLen oldHeader value hloadLen
      (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
      (by simpa [oldHeader] using hflag)
      (by simpa [oldHeader] using hbad)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
    exact bytesStoreLitePushChunkBodyRevertsOfPush (evm := evmSolm0) (value := value)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLitePushChunkShortMalformedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkShortMalformedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hflag hbad

theorem bytesStoreLiteDecode_set {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.bytes (BytesStoreLiteCore.setDecodedValueBytes I))) := by
  exact BytesStoreLiteCore.decodeCalldata_set_some
    (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList

theorem bytesStoreLiteSetCurrentShortPostAccountMapEquiv {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord)
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ (solidityShortBytesWord value)).accountMap := by
  simpa [initState, hstored] using
    accountMapEquiv_storageStore_initState_codeOwner
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts ⟨0⟩
      (solidityShortBytesWord value)

theorem bytesStoreLiteSetCurrentShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨0⟩ storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner ⟨0⟩ (solidityShortBytesWord value)).accountMap := by
  have hdivNat :
      (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩).toNat =
        (oldLen.toNat + 31) / 32 :=
    BytesStoreLiteCore.u256_div_add31_toNat_of_lt_sign (x := oldLen) holdLenLt
  have hcountNat :
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat =
        (oldLen.toNat + 31) / 32 := by
    rw [bytesStoreLite_shiftRight_five_eq_div_thirtyTwo,
      BytesStoreLiteCore.uint256_sub_zero_right]
    exact hdivNat
  simpa [u256_zero_add, BytesStoreLiteCore.uint256_add_zero_right] using
    BytesStoreLiteCore.accountMapEquiv_setCurrentShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (clearCount := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
      (storedWord := storedWord) (oldFuel := (oldLen.toNat + 31) / 32)
      (value := value) hAccounts hcountNat hstored

theorem bytesStoreLiteSetCurrentShortCreatedAccounts {cA gh bl σ_solm σ₀ A I}
    {g : UInt256} {value : ByteArray} :
    cA =
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ (solidityShortBytesWord value)).createdAccounts := by
  simp only [storageStore_createdAccounts, initState]

theorem bytesStoreLiteSetNewLongOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let dataFuel : Nat := (value.size + 31) / 32
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ value 0 dataFuel)
    (writeSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ value 0 dataFuel).executionEnv.codeOwner
    ⟨0⟩ header
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hretWord :
      UInt256.ofNat value.size = len := by
    rw [hsizeDecoded]
    exact u256_ofNat_toNat len
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hvalid
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreLiteWriteCurrentLongPacked (evm := evmSolm0)
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen)
      (value := value)
      hvalueSizeLong hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
    simpa [evmSolm0, evmSolm1, value, header, dataFuel, solidityBytesDataWordCount]
      using hwrite₀
  have hsolmMap :
      evmSolm1.accountMap =
        sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner σ_solm ⟨0⟩ value 0 dataFuel)
          ⟨0⟩ header := by
    simpa [evmSolm1, evmSolm0, dataFuel, initState] using
      storageStore_writeSolidityBytesDataWordsFrom_accountMap
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨0⟩ value 0 dataFuel ⟨0⟩ header
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  by_cases hmod : len.toNat % 32 = 0
  · have hret :
        RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_evm
              BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
              (BytesStoreLiteCore.clearCurrentBaseMemFrom
                (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreLiteX_setLongNoTailReturnsOldShortFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore hvalidCore hmod
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_evm
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_solm
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          BytesStoreLiteCore.accountMapEquiv_sstore_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := BytesStoreLiteCore.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len))
            (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32) (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hdataFuelEq : dataFuel = len.toNat / 32 := by
        dsimp [dataFuel]
        rw [hsizeDecoded]
        have hdiv := Nat.div_add_mod len.toNat 32
        omega
      have hdataBridge := BytesStoreLiteCore.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
        (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
        hnz hlenMaxLen hsrc hsizeDecoded (by rfl) (by rfl) hoffMax
        (τ := σ_solm) (i := 0) (fuel := len.toNat / 32) (by omega)
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_solm
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat 0 =
            BytesStoreLiteCore.clearCurrentBaseWord := by
          simpa using BytesStoreLiteCore.uint256_add_zero_right
            BytesStoreLiteCore.clearCurrentBaseWord
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [hdataFuelEq, hbase0, hstride] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap] using hret) hd hdec hwrite hCreated
      hAccountsPost henc
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((value).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((value).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        wordTail = UInt256.ofNat (fromBytesBigEndian
          (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    have hret :
        RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_evm
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                (len.toNat / 32))
              (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreLiteX_setLongTailReturnsOldShortFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (wordTail := wordTail)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore hvalidCore hmod
        (by rfl) (by rfl) hoffMax hwordTail
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_evm
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_solm
                  BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                  (BytesStoreLiteCore.clearCurrentBaseMemFrom
                    (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          BytesStoreLiteCore.accountMapEquiv_sstore_tail_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := BytesStoreLiteCore.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len))
            (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32)
            (tailSlot := BytesStoreLiteCore.longDataWordsLoopSlot
              BytesStoreLiteCore.clearCurrentBaseWord (len.toNat / 32))
            (tailWord := BytesStoreLiteCore.longDataTailMaskedWord wordTail len)
            (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
        dsimp [dataFuel]
        rw [hsizeDecoded]
        have hdiv := Nat.div_add_mod len.toNat 32
        have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      have hdataBridge := BytesStoreLiteCore.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
        (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
        (owner := I.codeOwner)
        hnz hlenMaxLen hsrc hsizeDecoded hlong (by rfl) (by rfl) hoffMax hmod (by rfl) σ_solm
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner σ_solm
                  BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                  (BytesStoreLiteCore.clearCurrentBaseMemFrom
                    (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat 0 =
            BytesStoreLiteCore.clearCurrentBaseWord := by
          simpa using BytesStoreLiteCore.uint256_add_zero_right
            BytesStoreLiteCore.clearCurrentBaseWord
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [hdataFuelEq, hbase0, hstride] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap] using hret) hd hdec hwrite hCreated
      hAccountsPost henc

theorem bytesStoreLiteSetNewShortOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart))
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩
    (solidityShortBytesWord value)
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord)
        (UInt256.toByteArray len) := by
    simpa [len, payloadStart, storedWord] using
      bytesStoreLiteX_setDecodeShortNonemptyReturnsCurrentHeader
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreLiteWriteCurrentDecodedShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts (by rfl) hpayloadList hnewShort hflag hvalid
    simpa [evmSolm0, evmSolm1, value, initState] using hwrite₀
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, len, payloadStart] using
      bytesStoreLiteSetHelperShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        (by rfl) (by rfl) hoffMax hnz hnewShort hsrc hpayloadList
  have hCreated : cA = evmSolm1.createdAccounts := by
    simpa [evmSolm1, evmSolm0, value, initState] using
      bytesStoreLiteSetCurrentShortCreatedAccounts
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (value := value)
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord)
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0, value, initState] using
      bytesStoreLiteSetCurrentShortPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (storedWord := storedWord) (value := value) hAccounts hstored
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    have hlenSize : len.toNat = value.size := by
      dsimp [value, len]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [← hlenSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (o := UInt256.toByteArray len)
    (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreLiteSetNewShortOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldLen : UInt256 := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (BytesStoreLiteCore.setHelperPayloadWord I.calldata len payloadStart))
  let τ : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ (solidityShortBytesWord value)
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hvalid
  have holdLenCore :
      oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord]
  have hbranch := bytesStoreLiteX_setShortLongHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hperm hdecodedReachLen hnz hnewShort (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hsrc hflagCore holdLenCore hvalidCore
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
        (UInt256.toByteArray len) := by
    simpa [τ, storedWord] using
      bytesStoreLiteX_setShortNonemptyWriteReturnAfterClearBase
        (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (τ := τ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart)
        hperm hbranch hnz hnewShort hsrc
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreLiteWriteCurrentDecodedShortFromLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts (by rfl) hpayloadList hnewShort hflag hvalid
    simpa [evmSolm0, evmSolm1, value, oldLen, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, len, payloadStart] using
      bytesStoreLiteSetHelperShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        (by rfl) (by rfl) hoffMax hnz hnewShort hsrc hpayloadList
  have holdLenLt : oldLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen) (by rfl)
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0, oldLen, value, τ, initState] using
      bytesStoreLiteSetCurrentShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    have hlenSize : len.toNat = value.size := by
      dsimp [value, len]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [← hlenSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (o := UInt256.toByteArray len)
    (acc := (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreLiteSetEmptyShortValidRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hvalid
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
        (UInt256.toByteArray ⟨0⟩) :=
    bytesStoreLiteX_setEmptyShortHeaderWriteReturn
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hperm hreach hflagCore hvalidCore
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreLiteWriteCurrentEmptyShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hflag hvalid
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int ByteArray.empty.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    (o := UInt256.toByteArray ⟨0⟩)
    (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreLiteWriteCurrentEmptyLongOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlen : oldLen = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
      I.codeOwner ⟨0⟩ ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ ⟨0⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite₀ := bytesStoreLiteWriteCurrentShortFromLongPrepared
    (evm := evmSolm0) (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I)
    (len := oldLen) (value := ByteArray.empty)
    (by decide) hload hflag hlen hvalid
  simpa [evmSolm0, evmSolm1, initState, hshortEmpty,
    clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀

theorem bytesStoreLiteSetCurrentEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨0⟩ ⟨0⟩)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner ⟨0⟩ ⟨0⟩).accountMap := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hstored : (⟨0⟩ : UInt256) = solidityShortBytesWord ByteArray.empty := hshortEmpty.symm
  simpa [initState, hshortEmpty] using
    bytesStoreLiteSetCurrentShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

set_option maxHeartbeats 4000000 in
theorem bytesStoreLiteSetEmptyLongValidRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let acc : Batteries.RBSet AccountAddress compare × AccountMap :=
    (cA, sstoreAccountMap I.codeOwner
      (clearDataWordsForwardFrom I.codeOwner σ_evm
        (⟨0⟩ + BytesStoreLiteCore.clearCurrentBaseWord) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
      ⟨0⟩ ⟨0⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ ⟨0⟩
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hvalid
  have holdLenCore :
      oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord]
  have hret : RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray ⟨0⟩) := by
    simpa [acc] using
      bytesStoreLiteX_setEmptyLongHeaderWriteReturn
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (payloadStart := payloadStart) (oldLen := oldLen)
        hperm hreach hflagCore holdLenCore hvalidCore
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreLiteWriteCurrentEmptyLongOfAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (oldLen := oldLen)
        hAccounts (by rfl) hflag (by simpa [oldLen] using hvalid)
  have holdLenLt : oldLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen) (by rfl)
  have hCreated : acc.1 = evmSolm1.createdAccounts := by
    simp [acc, evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv acc.2 evmSolm1.accountMap := by
    simpa [acc, evmSolm1, evmSolm0] using
      bytesStoreLiteSetCurrentEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (oldLen := oldLen)
        hAccounts holdLenLt
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int ByteArray.empty.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    (o := UInt256.toByteArray ⟨0⟩) (acc := acc) (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreLiteSetEmptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreLiteX_setEmptyLongMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hreach hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert := by
    have hwrite₀ := bytesStoreLiteWriteCurrentMalformedLongOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreLiteSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    hcode hwv hrev hd hdec hwrite

theorem bytesStoreLiteSetEmptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreLiteX_setEmptyShortMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hreach hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert := by
    have hwrite₀ := bytesStoreLiteWriteCurrentMalformedShortOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreLiteSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    hcode hwv hrev hd hdec hwrite

theorem bytesStoreLiteSetEmptyRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := BytesStoreLiteCore.decodeCalldata_set_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    rw [hlenZero]
    apply ugt_zero
    rw [u256_add_assoc]
    rw [show ((⟨0⟩ : UInt256) + ⟨32⟩) = ⟨32⟩ by native_decide]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hreach :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
        [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [payloadStart, hlenZero] using hdecodedReach
  by_cases hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetEmptyShortValidRuntimeOfReach
        hcode hperm hwv hAccounts hreach hd hdec hflag hvalid
    · exact bytesStoreLiteSetEmptyShortMalformedRuntimeOfReach
        hcode hwv hAccounts hreach hd hdec hflag (not_ne_iff.mp hvalid)
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetEmptyLongValidRuntimeOfReach
        hcode hperm hwv hAccounts hreach hd hdec hflag hvalid
    · exact bytesStoreLiteSetEmptyLongMalformedRuntimeOfReach
        hcode hwv hAccounts hreach hd hdec hflag (not_ne_iff.mp hvalid)

theorem bytesStoreLiteSetDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetSelector_size hsel
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_headShort (I := I) hsz hshort
  exact (bytesStoreLiteX_setDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetSelector_size hsel
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_huge (I := I) hbig
  exact (bytesStoreLiteX_setDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_offsetHuge (I := I) hsz36 hoff
  exact (bytesStoreLiteX_setDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_lengthShort
    (I := I) hsz36 hhi hlenShort
  exact (bytesStoreLiteX_setDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax hlenShort)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_lengthHuge
    (I := I) hsz36 hhi hoffMax hlenWord hlenHuge
  exact (bytesStoreLiteX_setDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_payloadShort
    (I := I) hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreLiteX_setDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
      hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetNewShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetNewShortOldShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
    · exact bytesStoreLiteSetRawDecodedNonemptyShortMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetNewShortOldLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
    · exact bytesStoreLiteSetRawDecodedNonemptyLongMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)

theorem bytesStoreLiteSetDecodedShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩
  · exact bytesStoreLiteSetEmptyRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenZero
  · have hlenAbi :
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) =
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
      simpa using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
    have hnz :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
      intro hz
      apply hlenZero
      apply u256_inj
      simpa [hlenAbi] using hz
    exact bytesStoreLiteSetNewShortRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
      hlenMax hpayloadList hpayloadWord hnz hnewShort

theorem bytesStoreLiteMappedLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 36
  · exact bytesStoreLiteMappedLengthDecodeShortRuntime hcode hsize hperm hwv hsel hshort
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact bytesStoreLiteMappedLengthRuntimeDecoded
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact bytesStoreLiteMappedLengthDecodeHugeRuntime hcode hsize hperm hwv hsel hbig

theorem bytesStoreLitePacketTagRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz := bytesStoreLitePacketTagSelector_size hsel
  have hreach := bytesStoreLiteReachPacketTag (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_packetTag (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_packetTag (I := I) hsz
  have hword : packetTagWord σ_evm I = packetTagWord σ_solm I :=
    packetTagWord_eq_of_accountMapEquiv hAccounts
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        packetTagGetter.body
        (.returned { contract := bytesStoreLiteContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (packetTagWord σ_solm I).toNat)))) := by
    simpa [packetTagWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      bytesStoreLitePacketTagBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (bytesStoreLiteX_packetTag (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (packetTagWord σ_evm I)))

theorem bytesStoreLiteCurrentLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteCurrentLengthSelector_size hsel
  have hreach := bytesStoreLiteReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact bytesStoreLiteCurrentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_currentLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCurrentLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteCurrentLengthSelector_size hsel
  have hreach := bytesStoreLiteReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact bytesStoreLiteCurrentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_currentLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteClearCurrentLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteClearCurrentSelector_size hsel
  have hreach := bytesStoreLiteReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_clearCurrent (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact bytesStoreLiteClearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_clearCurrentLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteClearCurrentShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteClearCurrentSelector_size hsel
  have hreach := bytesStoreLiteReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_clearCurrent (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact bytesStoreLiteClearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_clearCurrentShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteClearCurrentShortZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hheader : bytesStoreLiteCurrentLengthHeaderWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsz := bytesStoreLiteClearCurrentSelector_size hsel
  have hd := bytesStoreLiteDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    decide
  have hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hheader]
    decide
  have hzero : UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ =
      ⟨0⟩ := by
    rw [hheader]
    decide
  have hret := bytesStoreLiteX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hvalid hzero
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hload' :
        Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
          bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
      simpa [evmSolm0, initState] using
        bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts
    simpa [hheader] using hload'
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    simpa [evmSolm0, initState] using hload
  have hread :
      evalExpr? bytesStoreLiteConfig { contract := bytesStoreLiteContract, locals := ∅ }
        evmSolm0 (.storage currentRef) = .ok (.bytes ByteArray.empty) := by
    exact evalSolidityBytesEmptyOfZeroHeader
      (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
      (solm := { contract := bytesStoreLiteContract, locals := ∅ })
      (evm := evmSolm0) (ref := currentRef) (er := { base := "current" })
      (baseSlot := ⟨0⟩)
      rfl (bytesStoreLiteCurrentLengthResolve evmSolm0)
      bytesStoreLiteCurrentLengthBaseSlot hloadBytes
  have hdel :
      deleteStorage? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteDeleteCurrentShortZero (evm := evmSolm0) hload
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
          evmSolm1 (some (.int 0))) := by
    exact bytesStoreLiteClearCurrentBodyReturnsZero (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hread hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simpa [evmSolm1, evmSolm0] using
        accountMapEquiv_storageStore_initState_codeOwner
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreLiteClearCurrentShortNonzeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsz := bytesStoreLiteClearCurrentSelector_size hsel
  have hd := bytesStoreLiteDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hret := bytesStoreLiteX_clearCurrentShortValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hlen hvalid hnonzero
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  obtain ⟨copy, hread, hcopySize⟩ :=
    bytesStoreLiteReadCurrentShortPackedExists (evm := evmSolm0)
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := len)
      hloadBytes hflag hlen hvalid
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hdel :
      deleteStorage? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteDeleteCurrentShortPacked (evm := evmSolm0)
        (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := len) (copy := copy)
        hloadBytes hpacked hflag hlen hvalid
  have hbodyBytes := bytesStoreLiteClearCurrentBodyReturnsBytes
    (evm := evmSolm0) (evm' := evmSolm1) (copy := copy)
    (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int len.toNat))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simpa [evmSolm1, evmSolm0] using
        accountMapEquiv_storageStore_initState_codeOwner
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))
    (returnEquiv_of_encode (uint256ReturnEncoding len))

theorem bytesStoreLiteCurrentLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteCurrentLengthSelector_size hsel
  have hreach := bytesStoreLiteReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat :=
    bytesStoreLiteReadCurrentLengthLong_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreLiteContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreLiteCurrentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_currentLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreLiteCurrentLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteCurrentLengthSelector_size hsel
  have hreach := bytesStoreLiteReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreLiteDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat :=
    bytesStoreLiteReadCurrentLengthShort_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreLiteContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat
              (UInt256.land
                (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreLiteCurrentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_currentLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreLiteCurrentLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteCurrentLengthShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteCurrentLengthShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteCurrentLengthLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteCurrentLengthLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad

theorem bytesStoreLitePacketLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz := bytesStoreLitePacketLengthSelector_size hsel
  have hreach := bytesStoreLiteReachPacketLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_packetLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_packetLength (I := I) hsz
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [bytesStoreLitePacketLengthHeaderWord, initState] using
      bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) ⟨2⟩ hAccounts
  by_cases hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · have hvalid0 :
          UInt256.sub ⟨0⟩
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
        simpa [hflag] using hvalid
      have hlen :
          readStorageBytesLength? bytesStoreLiteConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } =
              .ok (UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
        exact bytesStoreLiteReadLengthOfHeaderLoad
          (er := bytesStoreLitePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
          (len := (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
          (bytesStoreLitePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
      have hbody :
          ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body
            (.returned { contract := bytesStoreLiteContract, locals := ∅ }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some (.int
                (Int.ofNat
                  (UInt256.land
                    (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
        exact bytesStoreLitePacketLengthBodyReturnsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreLiteX_packetLengthShortValid
          (g := Sat256.ofUInt256 g) hreach hflag hvalid)
        |>.reEquivExecution hcode hd hdec hbody hAccounts
          (returnEquiv_of_encode
            (uint256ReturnEncoding
              (UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      have hbad0 :
          UInt256.sub ⟨0⟩
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
        simpa [hflag] using hbad
      have hlen :
          readStorageBytesLength? bytesStoreLiteConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } = .revert := by
        exact bytesStoreLiteReadLengthRevertOfHeaderLoad
          (er := bytesStoreLitePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
          (bytesStoreLitePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
      have hbody :
          ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body .reverted := by
        exact bytesStoreLitePacketLengthBodyRevertsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreLiteX_packetLengthShortMalformed
          (g := Sat256.ofUInt256 g) hreach hflag hbad)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · have hlen :
          readStorageBytesLength? bytesStoreLiteConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } =
              .ok (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
        exact bytesStoreLiteReadLengthOfHeaderLoad
          (er := bytesStoreLitePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
          (len := (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
          (bytesStoreLitePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
      have hbody :
          ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body
            (.returned { contract := bytesStoreLiteContract, locals := ∅ }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some (.int
                (Int.ofNat (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
        exact bytesStoreLitePacketLengthBodyReturnsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreLiteX_packetLengthLongValid
          (g := Sat256.ofUInt256 g) hreach hflag hvalid)
        |>.reEquivExecution hcode hd hdec hbody hAccounts
          (returnEquiv_of_encode
            (uint256ReturnEncoding (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)))
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      have hlen :
          readStorageBytesLength? bytesStoreLiteConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } = .revert := by
        exact bytesStoreLiteReadLengthRevertOfHeaderLoad
          (er := bytesStoreLitePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
          (bytesStoreLitePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
      have hbody :
          ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body .reverted := by
        exact bytesStoreLitePacketLengthBodyRevertsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreLiteX_packetLengthLongMalformed
          (g := Sat256.ofUInt256 g) hreach hflag hbad)
        |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStoreLite
