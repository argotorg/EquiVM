import Examples.BytesStore.Dispatch
import Examples.BytesStore.StorageReadbackFacts
import Examples.StringStoreLite.SetLong
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
# BytesStore — full-runtime `packetTag()` slice

This file starts the optimized full-contract runtime proof with the simplest branch:
`packetTag()`, a scalar `uint256` getter at storage slot 3.  The dispatcher proof follows the
binary-search selector tree emitted by solc for the 15-function contract.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStore

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev bytesStoreSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

theorem decodeCalldata_set_none_headShort {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen4 : ¬ I.calldata.toList.length < 4 := by
    omega
  have hnotRead : ¬ 32 ≤ I.calldata.toList.length - 4 := by
    omega
  have hread : ABI.readNat? (I.calldata.toList.drop 4) 0 = none := by
    unfold ABI.readNat? ABI.readWord? ABI.readBytes?
    simp [hnotRead]
  rw [if_neg hlen4]
  have hnotDyn :
      ¬ ([ABIType.bytes].any ABI.isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    intro h
    rw [htlen] at h
    omega
  rw [if_neg hnotDyn]
  have hnotHuge :
      ¬ ([ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  rw [if_neg hnotHuge]
  by_cases htotalHuge :
      ABI.solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧
        2 ^ 255 ≤ I.calldata.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    simp [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hread, bind, Option.bind_none, Option.bind_some]

theorem decodeCalldata_set_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_huge (x := "value") hbig

theorem decodeCalldata_set_none_totalHigh {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_total_huge (x := "value") hbig

theorem decodeCalldata_set_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_offset_huge (x := "value") hsz36 hoff

theorem decodeCalldata_set_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_short (x := "value") hsz36 hhi hshort

theorem decodeCalldata_set_none_lengthHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_huge (x := "value") hsz36 hhi hoffMax hlenWord
    hlenHuge

theorem decodeCalldata_set_none_payloadShort {I : ExecutionEnv}
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
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_payload_short (x := "value") hsz36 hhi hoffMax hlenWord
    hlenMax hpayload

theorem decodeCalldata_set_empty {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
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

theorem decodeCalldata_set_some {I : ExecutionEnv}
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
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "value" (.bytes (StringStoreLite.setDecodedValueBytes I))) := by
  show decodeCalldata ["value"] [.bytes] I.calldata =
      some ((∅ : Store).insert "value" (.bytes (StringStoreLite.setDecodedValueBytes I)))
  simpa [StringStoreLite.setDecodedValueBytes] using
    decodeCalldata_bytes_some (cd := I.calldata) (x := "value")
      hsz36 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem accountMapEquiv_sstore_header_after_longDataWordsForwardFrom
    {owner : AccountAddress} {σ τ : AccountMap}
    {slot stride ptr aw headerSlot header : UInt256} {mem : ByteArray} {fuel : Nat}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (StringStoreLite.longDataWordsForwardFrom owner σ slot stride ptr aw mem fuel)
        headerSlot header)
      (sstoreAccountMap owner
        (StringStoreLite.longDataWordsForwardFrom owner τ slot stride ptr aw mem fuel)
        headerSlot header) := by
  exact accountMapEquiv_sstoreAccountMap owner headerSlot header
    (StringStoreLite.accountMapEquiv_longDataWordsForwardFrom fuel hAccounts)

theorem accountMapEquiv_sstore_tail_header_after_longDataWordsForwardFrom
    {owner : AccountAddress} {σ τ : AccountMap}
    {slot stride ptr aw tailSlot tailWord headerSlot header : UInt256}
    {mem : ByteArray} {fuel : Nat}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (sstoreAccountMap owner
          (StringStoreLite.longDataWordsForwardFrom owner σ slot stride ptr aw mem fuel)
          tailSlot tailWord)
        headerSlot header)
      (sstoreAccountMap owner
        (sstoreAccountMap owner
          (StringStoreLite.longDataWordsForwardFrom owner τ slot stride ptr aw mem fuel)
          tailSlot tailWord)
        headerSlot header) := by
  exact accountMapEquiv_sstoreAccountMap owner headerSlot header
    (accountMapEquiv_sstoreAccountMap owner tailSlot tailWord
      (StringStoreLite.accountMapEquiv_longDataWordsForwardFrom fuel hAccounts))

/-! ## Dispatcher path for `packetTag()` -/

abbrev bytesStoreSplitPc : UInt256 := ⟨30⟩
abbrev bytesStoreHighSplitPc : UInt256 := ⟨41⟩
abbrev bytesStoreHighFirstArmPc : UInt256 := ⟨52⟩
abbrev bytesStoreMidLowJumpdestPc : UInt256 := ⟨99⟩
abbrev bytesStoreMidLowFirstArmPc : UInt256 := ⟨100⟩
abbrev bytesStoreRootLowJumpdestPc : UInt256 := ⟨147⟩
abbrev bytesStoreLowSplitPc : UInt256 := ⟨148⟩
abbrev bytesStoreLowFallthroughFirstArmPc : UInt256 := ⟨159⟩
abbrev bytesStoreLowTakenJumpdestPc : UInt256 := ⟨206⟩
abbrev bytesStoreLowTakenFirstArmPc : UInt256 := ⟨207⟩

def bytesStoreMidLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩
  | 1 => ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩
  | 2 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩
  | _ => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩

def bytesStoreHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩
  | 1 => ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩
  | 2 => ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩
  | _ => ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩

def bytesStoreLowFallthroughSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩
  | 1 => ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩
  | 2 => ⟨#[0x39, 0x1d, 0x72, 0x80]⟩
  | _ => ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩

def bytesStoreLowTakenSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x03, 0x99, 0x32, 0x1e]⟩
  | 1 => ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩
  | _ => ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩

theorem bytesStoreSplitWellFormed :
    selectorSplitWellFormed bytesStoreBytecode bytesStoreSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreHighSplitWellFormed :
    selectorSplitWellFormed bytesStoreBytecode bytesStoreHighSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreLowSplitWellFormed :
    selectorSplitWellFormed bytesStoreBytecode bytesStoreLowSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreMidLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLowFallthroughArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreLowTakenArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem bytesStoreSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    bytesStoreSelWord I = sel := by
  apply u256_inj
  dsimp [bytesStoreSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem bytesStoreMidLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc j))
        (bytesStoreSelWord I) =
      if (bytesStoreMidLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc j))
        (bytesStoreSelWord I) =
      if (bytesStoreHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLowFallthroughArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc j))
        (bytesStoreSelWord I) =
      if (bytesStoreLowFallthroughSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreLowTakenArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc j))
        (bytesStoreSelWord I) =
      if (bytesStoreLowTakenSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem bytesStoreMidLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreMidLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc i))
        (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreMidLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreMidLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreMidLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc i))
        (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLowFallthroughMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLowFallthroughSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc i))
        (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLowFallthroughSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLowFallthroughArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLowFallthroughArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLowTakenMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLowTakenSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc i))
        (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLowTakenSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLowTakenArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLowTakenArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreSetFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I = ⟨0x0399321e⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x03 0x99 0x32 0x1e _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreSetSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreLowSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I = ⟨0x0399321e⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x03 0x99 0x32 0x1e _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePacketTagFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2570979984⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x99 0x3e 0x0a 0x90 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePacketTagSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2570979984⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x99 0x3e 0x0a 0x90 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreCurrentLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2748538678⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xa3 0xd3 0x5f 0x36 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreCurrentLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2748538678⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xa3 0xd3 0x5f 0x36 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreClearCurrentFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2799673954⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xa6 0xdf 0xa2 0x62 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreClearCurrentSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨2799673954⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xa6 0xdf 0xa2 0x62 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePushChunkFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3037513900⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xb5 0x0c 0xc8 0xac _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePushChunkSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3037513900⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xb5 0x0c 0xc8 0xac _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePacketLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3038302916⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xb5 0x18 0xd2 0xc4 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStorePacketLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3038302916⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xb5 0x18 0xd2 0xc4 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreMappedLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨958231168⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x39 0x1d 0x72 0x80 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreMappedLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreLowSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨958231168⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0x39 0x1d 0x72 0x80 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreChunkLengthFirstPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3904740085⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xe8 0xbd 0x9a 0xf5 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreChunkLengthSecondPivot {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩ := by
  have hword : bytesStoreSelWord I =
      ⟨3904740085⟩ :=
    bytesStoreSelWord_eq_of_beq I hsz 0xe8 0xbd 0x9a 0xf5 _ (by native_decide)
      (by simpa [selIs] using hsel)
  rw [hword]
  native_decide

theorem bytesStoreSolcDispatchPrefix :
    solcDispatchPrefixWellFormed bytesStoreBytecode bytesStoreSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem bytesStoreSplitNextPc :
    selArmNextPc bytesStoreSplitPc
      (armTgtWidth bytesStoreBytecode bytesStoreSplitPc) =
    bytesStoreHighSplitPc := by
  native_decide

theorem bytesStoreHighSplitTgt :
    armTgt bytesStoreBytecode bytesStoreHighSplitPc =
    bytesStoreMidLowJumpdestPc := by
  native_decide

theorem bytesStoreHighSplitNextPc :
    selArmNextPc bytesStoreHighSplitPc
      (armTgtWidth bytesStoreBytecode bytesStoreHighSplitPc) =
    bytesStoreHighFirstArmPc := by
  native_decide

theorem bytesStoreSplitTgt :
    armTgt bytesStoreBytecode bytesStoreSplitPc =
    bytesStoreRootLowJumpdestPc := by
  native_decide

theorem bytesStoreLowSplitNextPc :
    selArmNextPc bytesStoreLowSplitPc
      (armTgtWidth bytesStoreBytecode bytesStoreLowSplitPc) =
    bytesStoreLowFallthroughFirstArmPc := by
  native_decide

theorem bytesStoreLowSplitTgt :
    armTgt bytesStoreBytecode bytesStoreLowSplitPc =
    bytesStoreLowTakenJumpdestPc := by
  native_decide

theorem bytesStoreHighArmsEnd :
    nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc 4 = ⟨96⟩ := by
  native_decide

theorem bytesStoreMidLowArmsEnd :
    nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc 4 = ⟨144⟩ := by
  native_decide

theorem bytesStoreLowFallthroughArmsEnd :
    nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 4 = ⟨203⟩ := by
  native_decide

theorem bytesStoreLowTakenArmsEnd :
    nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 3 = ⟨240⟩ := by
  native_decide

theorem bytesStoreReachPacketTag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePacketTagFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePacketTagSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreMidLowFirstArmPc, bytesStoreMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreMidLowMatches 1 (by decide) hsz
      (by simpa [selIs, bytesStoreMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨433⟩ 1 hfirstRD
    (fun j hj => bytesStoreMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachCurrentLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨441⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreCurrentLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreCurrentLengthSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreMidLowFirstArmPc, bytesStoreMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreMidLowMatches 2 (by decide) hsz
      (by simpa [selIs, bytesStoreMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨441⟩ 2 hfirstRD
    (fun j hj => bytesStoreMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachClearCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨449⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreClearCurrentFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreClearCurrentSecondPivot (I := I) hsz hsel)
        (by native_decide) (by simp)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreMidLowFirstArmPc, bytesStoreMidLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreMidLowMatches 3 (by decide) hsz
      (by simpa [selIs, bytesStoreMidLowSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨449⟩ 3 hfirstRD
    (fun j hj => bytesStoreMidLowArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachPushChunk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨457⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePushChunkFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePushChunkSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreHighMatches 0 (by decide) hsz
      (by simpa [selIs, bytesStoreHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨457⟩ 0 hfirstRD
    (fun j hj => bytesStoreHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachPacketLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨476⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePacketLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStorePacketLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreHighMatches 1 (by decide) hsz
      (by simpa [selIs, bytesStoreHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨476⟩ 1 hfirstRD
    (fun j hj => bytesStoreHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachChunkLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨503⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreChunkLengthFirstPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreChunkLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreHighMatches 3 (by decide) hsz
      (by simpa [selIs, bytesStoreHighSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨503⟩ 3 hfirstRD
    (fun j hj => bytesStoreHighArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachMappedLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨376⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreRootLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreMappedLengthFirstPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLowSplitPc, bytesStoreRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowFallthroughFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hlowSplit bytesStoreLowSplitWellFormed
        (by
          simpa [bytesStoreSelWord, solcSelectorWord] using
            bytesStoreMappedLengthSecondPivot (I := I) hsz hsel)
        (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLowFallthroughMatches 2 (by decide) hsz
      (by simpa [selIs, bytesStoreLowFallthroughSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo ⟨376⟩ 2 hfirstRD
    (fun j hj => bytesStoreLowFallthroughArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) (by native_decide) (by simp)

theorem bytesStoreReachSet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 0))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreRootLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreSplitWellFormed
        (bytesStoreSetFirstPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLowSplitPc, bytesStoreRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hlowTakenJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowTakenJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hlowSplit bytesStoreLowSplitWellFormed
        (bytesStoreSetSecondPivot (I := I) hsz hsel)
        (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitTgt] using hstep
  obtain ⟨kT, CT, hlowTakenJdRD⟩ := hlowTakenJd
  have hfirst : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowTakenFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kT + 1, CT + 1, ?_⟩
    simpa [bytesStoreLowTakenFirstArmPc, bytesStoreLowTakenJumpdestPc] using
      hlowTakenJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirst
  rcases bytesStoreLowTakenMatches 0 (by decide) hsz
      (by simpa [selIs, bytesStoreLowTakenSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 0))
    0 hfirstRD
    (fun j hj => bytesStoreLowTakenArmsWellFormed j (le_trans hj (by decide)))
    heq0 htake (by native_decide) rfl (by simp)

theorem bytesStoreReachHighArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩)
    (hsel : (bytesStoreHighSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc i))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        hfirst (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have harm0 : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        hsecond (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := harm0
  rcases bytesStoreHighMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreReachMidLowArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
        (bytesStoreSelWord I) ≠ ⟨0⟩)
    (hsel : (bytesStoreMidLowSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc i))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hhigh : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreHighSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed
        hfirst (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using hstep
  obtain ⟨kH, CH, hhighSplit⟩ := hhigh
  have hmidJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kH + 5, CH + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hhighSplit bytesStoreHighSplitWellFormed
        hsecond (by native_decide) (by simp)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitTgt] using hstep
  obtain ⟨kJ, CJ, hmidJdRD⟩ := hmidJd
  have hfirstArm : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreMidLowFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreMidLowFirstArmPc, bytesStoreMidLowJumpdestPc] using
      hmidJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreMidLowMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreMidLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreReachLowFallthroughArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 4)
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
        (bytesStoreSelWord I) ≠ ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreLowSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩)
    (hsel : (bytesStoreLowFallthroughSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc i))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreRootLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreSplitWellFormed
        hfirst (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLowSplitPc, bytesStoreRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have hfirstArm : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowFallthroughFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitNotTakenAuto hlowSplit bytesStoreLowSplitWellFormed
        hsecond (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitNextPc] using hstep
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreLowFallthroughMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLowFallthroughArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreReachLowTakenArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i < 3)
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfirst :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
        (bytesStoreSelWord I) ≠ ⟨0⟩)
    (hsecond :
      UInt256.gt (armSelNat bytesStoreBytecode bytesStoreLowSplitPc)
        (bytesStoreSelWord I) ≠ ⟨0⟩)
    (hsel : (bytesStoreLowTakenSelBytes i == I.calldata.extract 0 4) = true) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc i))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize
    bytesStoreSolcDispatchPrefix (by native_decide)
  have hlowJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreRootLowJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hsplit bytesStoreSplitWellFormed
        hfirst (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitTgt] using hstep
  obtain ⟨kJ, CJ, hlowJdRD⟩ := hlowJd
  have hlow : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowSplitPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJ + 1, CJ + 1, ?_⟩
    simpa [bytesStoreLowSplitPc, bytesStoreRootLowJumpdestPc] using
      hlowJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨kL, CL, hlowSplit⟩ := hlow
  have htakenJd : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowTakenJumpdestPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kL + 5, CL + 22, ?_⟩
    have hstep := RD.selectorSplitTakenAuto hlowSplit bytesStoreLowSplitWellFormed
        hsecond (by native_decide) (by native_decide)
    simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitTgt] using hstep
  obtain ⟨kT, CT, htakenJdRD⟩ := htakenJd
  have hfirstArm : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
      bytesStoreLowTakenFirstArmPc [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kT + 1, CT + 1, ?_⟩
    simpa [bytesStoreLowTakenFirstArmPc, bytesStoreLowTakenJumpdestPc] using
      htakenJdRD.jumpdest (by native_decide) (by simp)
  obtain ⟨_, _, hfirstRD⟩ := hfirstArm
  rcases bytesStoreLowTakenMatches i hi hsz hsel with ⟨heq0, htake⟩
  exact RD.dispatchTo
    (armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc i))
    i hfirstRD
    (fun j hj => bytesStoreLowTakenArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by interval_cases i <;> native_decide) rfl (by simp)

theorem bytesStoreSelectorPivot_eq0 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (sel : ByteArray) (c0 c1 c2 c3 : UInt8) (word : UInt256)
    (hsel : selIs I sel)
    (hselLit : sel = ⟨#[c0, c1, c2, c3]⟩)
    (hword : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = word.toNat)
    (pc : UInt256)
    (h : UInt256.gt (armSelNat bytesStoreBytecode pc) word = ⟨0⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode pc) (bytesStoreSelWord I) = ⟨0⟩ := by
  have hw : bytesStoreSelWord I = word := by
    subst hselLit
    exact bytesStoreSelWord_eq_of_beq I hsz c0 c1 c2 c3 word hword
      (by simpa [selIs] using hsel)
  simpa [hw] using h

theorem bytesStoreSelectorPivot_ne0 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (sel : ByteArray) (c0 c1 c2 c3 : UInt8) (word : UInt256)
    (hsel : selIs I sel)
    (hselLit : sel = ⟨#[c0, c1, c2, c3]⟩)
    (hword : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = word.toNat)
    (pc : UInt256)
    (h : UInt256.gt (armSelNat bytesStoreBytecode pc) word ≠ ⟨0⟩) :
    UInt256.gt (armSelNat bytesStoreBytecode pc) (bytesStoreSelWord I) ≠ ⟨0⟩ := by
  have hw : bytesStoreSelWord I = word := by
    subst hselLit
    exact bytesStoreSelWord_eq_of_beq I hsz c0 c1 c2 c3 word hword
      (by simpa [selIs] using hsel)
  simpa [hw] using h

theorem bytesStoreReachSetByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 1))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachLowFallthroughArm 1 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_ne0 hsz _ 0x1c 0x52 0x47 0x7d ⟨0x1c52477d⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_eq0 hsz _ 0x1c 0x52 0x47 0x7d ⟨0x1c52477d⟩
      hsel rfl (by native_decide) bytesStoreLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLowFallthroughSelBytes] using hsel)

theorem bytesStoreReachSetChunk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 3))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachLowFallthroughArm 3 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_ne0 hsz _ 0x39 0x3d 0x9c 0xd7 ⟨0x393d9cd7⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_eq0 hsz _ 0x39 0x3d 0x9c 0xd7 ⟨0x393d9cd7⟩
      hsel rfl (by native_decide) bytesStoreLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLowFallthroughSelBytes] using hsel)

theorem bytesStoreReachSetChunkByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc 0))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachMidLowArm 0 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_eq0 hsz _ 0x48 0x1c 0x2f 0xfb ⟨0x481c2ffb⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_ne0 hsz _ 0x48 0x1c 0x2f 0xfb ⟨0x481c2ffb⟩
      hsel rfl (by native_decide) bytesStoreHighSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreMidLowSelBytes] using hsel)

theorem bytesStoreReachSetPacket {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 0))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachLowFallthroughArm 0 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_ne0 hsz _ 0x14 0xf1 0x7c 0x69 ⟨0x14f17c69⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_eq0 hsz _ 0x14 0xf1 0x7c 0x69 ⟨0x14f17c69⟩
      hsel rfl (by native_decide) bytesStoreLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLowFallthroughSelBytes] using hsel)

theorem bytesStoreReachSetPacketByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 1))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachLowTakenArm 1 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_ne0 hsz _ 0x0a 0xb2 0x59 0x00 ⟨0x0ab25900⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_ne0 hsz _ 0x0a 0xb2 0x59 0x00 ⟨0x0ab25900⟩
      hsel rfl (by native_decide) bytesStoreLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLowTakenSelBytes] using hsel)

theorem bytesStoreReachSetMapped {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc 2))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachHighArm 2 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_eq0 hsz _ 0xe1 0x91 0x9b 0x17 ⟨0xe1919b17⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_eq0 hsz _ 0xe1 0x91 0x9b 0x17 ⟨0xe1919b17⟩
      hsel rfl (by native_decide) bytesStoreHighSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreHighSelBytes] using hsel)

theorem bytesStoreReachSetMappedByte {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 2))
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  bytesStoreReachLowTakenArm 2 (by decide)
    hcode hwv hsz hsize
    (bytesStoreSelectorPivot_ne0 hsz _ 0x13 0x2f 0xa3 0x46 ⟨0x132fa346⟩
      hsel rfl (by native_decide) bytesStoreSplitPc (by native_decide))
    (bytesStoreSelectorPivot_ne0 hsz _ 0x13 0x2f 0xa3 0x46 ⟨0x132fa346⟩
      hsel rfl (by native_decide) bytesStoreLowSplitPc (by native_decide))
    (by simpa [selIs, bytesStoreLowTakenSelBytes] using hsel)

theorem bytesStoreSetEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 0) = ⟨244⟩ := by
  native_decide

theorem bytesStoreSetByteEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 1) = ⟨357⟩ := by
  native_decide

theorem bytesStoreSetChunkEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 3) = ⟨395⟩ := by
  native_decide

theorem bytesStoreSetChunkByteEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc 0) = ⟨414⟩ := by
  native_decide

theorem bytesStoreSetPacketEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 0) = ⟨338⟩ := by
  native_decide

theorem bytesStoreSetPacketByteEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 1) = ⟨282⟩ := by
  native_decide

theorem bytesStoreSetMappedEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc 2) = ⟨484⟩ := by
  native_decide

theorem bytesStoreSetMappedByteEntryPc :
    armTgt bytesStoreBytecode
      (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 2) = ⟨319⟩ := by
  native_decide

theorem bytesStoreReachSetEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨244⟩
        [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  simpa [bytesStoreSetEntryPc] using
    (bytesStoreReachSet (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel)

theorem bytesStoreReachSetDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1883⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨258⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreReachSetEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨258⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨1883⟩, jump (by native_decide)])⟩

/-! ## No-dispatch short calldata -/

theorem bytesStoreX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt bytesStoreBytecode)
    (opC := solcGuardTgtOp bytesStoreBytecode)
    (wC := solcGuardTgtWidth bytesStoreBytecode)
    (solcGuardPrologueRD hcode (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide))
    hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreBodyReverts_nonPayable
    (t : TransitionDecl) (ht : t ∈ bytesStoreContract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm locals t.body .reverted := by
  rw [bytesStoreTransitions] at ht
  simp at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  all_goals subst t
  all_goals exact bodyReverts_nonPayable h

theorem bytesStoreNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (bytesStoreX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg bytesStoreContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ bytesStoreContract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (bytesStoreBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem bytesStoreX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt bytesStoreBytecode)
    (opC := solcGuardTgtOp bytesStoreBytecode)
    (wC := solcGuardTgtWidth bytesStoreBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc bytesStoreBytecode)
    (rtgt := solcCalldataRevertTgt bytesStoreBytecode)
    (opR := solcCalldataRevertTgtOp bytesStoreBytecode)
    (wR := solcCalldataRevertTgtWidth bytesStoreBytecode)
    h1 hsz (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hshort : I.calldata.size < 4) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact (bytesStoreX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch
      hcode (bytesStoreDispatch_none_short hshort)
  · exact bytesStoreNonPayable hcode hwv

theorem bytesStoreX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 15 → (bytesStoreSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreHighSelBytes, bytesStoreSelBytes] using hnm 4 (by omega)
      rw [bytesStoreHighArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreHighSelBytes, bytesStoreSelBytes] using hnm 10 (by omega)
      rw [bytesStoreHighArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreHighSelBytes, bytesStoreSelBytes] using hnm 12 (by omega)
      rw [bytesStoreHighArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreHighSelBytes, bytesStoreSelBytes] using hnm 7 (by omega)
      rw [bytesStoreHighArmEq I hsz 3 (by omega), hm]
      rfl
  have heqMidLow0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreMidLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreMidLowSelBytes, bytesStoreSelBytes] using hnm 6 (by omega)
      rw [bytesStoreMidLowArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreMidLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreMidLowSelBytes, bytesStoreSelBytes] using hnm 11 (by omega)
      rw [bytesStoreMidLowArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreMidLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreMidLowSelBytes, bytesStoreSelBytes] using hnm 3 (by omega)
      rw [bytesStoreMidLowArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreMidLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreMidLowSelBytes, bytesStoreSelBytes] using hnm 2 (by omega)
      rw [bytesStoreMidLowArmEq I hsz 3 (by omega), hm]
      rfl
  have heqLowFallthrough0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLowFallthroughSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowFallthroughSelBytes, bytesStoreSelBytes] using hnm 8 (by omega)
      rw [bytesStoreLowFallthroughArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLowFallthroughSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowFallthroughSelBytes, bytesStoreSelBytes] using hnm 1 (by omega)
      rw [bytesStoreLowFallthroughArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLowFallthroughSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowFallthroughSelBytes, bytesStoreSelBytes] using hnm 14 (by omega)
      rw [bytesStoreLowFallthroughArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (bytesStoreLowFallthroughSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowFallthroughSelBytes, bytesStoreSelBytes] using hnm 5 (by omega)
      rw [bytesStoreLowFallthroughArmEq I hsz 3 (by omega), hm]
      rfl
  have heqLowTaken0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat bytesStoreBytecode
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc j))
        (bytesStoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (bytesStoreLowTakenSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowTakenSelBytes, bytesStoreSelBytes] using hnm 0 (by omega)
      rw [bytesStoreLowTakenArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (bytesStoreLowTakenSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowTakenSelBytes, bytesStoreSelBytes] using hnm 9 (by omega)
      rw [bytesStoreLowTakenArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (bytesStoreLowTakenSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLowTakenSelBytes, bytesStoreSelBytes] using hnm 13 (by omega)
      rw [bytesStoreLowTakenArmEq I hsz 2 (by omega), hm]
      rfl
  obtain ⟨kS, CS, hsplit⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreBytecode) (firstPc := bytesStoreSplitPc)
    hcode hwv hsz hsize bytesStoreSolcDispatchPrefix (by native_decide)
  by_cases hpivot0 : UInt256.gt (armSelNat bytesStoreBytecode bytesStoreSplitPc)
      (bytesStoreSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit bytesStoreSplitWellFormed hpivot0
      (by native_decide)
    have h41' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreHighSplitPc [bytesStoreSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5, CS + 22, ?_⟩
      simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitNextPc] using h41
    obtain ⟨kH, CH, hhigh⟩ := h41'
    by_cases hpivot1 : UInt256.gt (armSelNat bytesStoreBytecode bytesStoreHighSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩
    · have h52 := RD.selectorSplitNotTakenAuto hhigh bytesStoreHighSplitWellFormed hpivot1
        (by native_decide)
      have h52' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreHighFirstArmPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kH + 5, CH + 22, ?_⟩
        simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitNextPc] using h52
      obtain ⟨k52, C52, h52rd⟩ := h52'
      have h96 := h52rd
        |>.selectorArmNotTakenAuto (bytesStoreHighArmsWellFormed 0 (by omega))
            (heqHigh0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreHighArmsWellFormed 1 (by omega))
            (heqHigh0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreHighArmsWellFormed 2 (by omega))
            (heqHigh0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreHighArmsWellFormed 3 (by omega))
            (heqHigh0 3 (by omega)) (by native_decide)
      have h96rd : RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨96⟩ [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k52 + 5 + 5 + 5 + 5) (C52 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreBytecode bytesStoreHighFirstArmPc 4)
          [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k52 + 5 + 5 + 5 + 5) (C52 + 22 + 22 + 22 + 22) at h96
        simpa [bytesStoreHighArmsEnd] using h96
      exact h96rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have h99 := RD.selectorSplitTakenAuto hhigh bytesStoreHighSplitWellFormed hpivot1
        (by native_decide) (by native_decide)
      have h99' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreMidLowJumpdestPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kH + 5, CH + 22, ?_⟩
        simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreHighSplitTgt] using h99
      obtain ⟨kJ, CJ, h99rd⟩ := h99'
      have h100 : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreMidLowFirstArmPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kJ + 1, CJ + 1, ?_⟩
        simpa [bytesStoreMidLowFirstArmPc, bytesStoreMidLowJumpdestPc] using
          h99rd.jumpdest (by native_decide) (by simp)
      obtain ⟨k100, C100, h100rd⟩ := h100
      have h144 := h100rd
        |>.selectorArmNotTakenAuto (bytesStoreMidLowArmsWellFormed 0 (by omega))
            (heqMidLow0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreMidLowArmsWellFormed 1 (by omega))
            (heqMidLow0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreMidLowArmsWellFormed 2 (by omega))
            (heqMidLow0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreMidLowArmsWellFormed 3 (by omega))
            (heqMidLow0 3 (by omega)) (by native_decide)
      have h144rd : RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨144⟩ [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k100 + 5 + 5 + 5 + 5) (C100 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreBytecode bytesStoreMidLowFirstArmPc 4)
          [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k100 + 5 + 5 + 5 + 5) (C100 + 22 + 22 + 22 + 22) at h144
        simpa [bytesStoreMidLowArmsEnd] using h144
      exact h144rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · have h147 := RD.selectorSplitTakenAuto hsplit bytesStoreSplitWellFormed hpivot0
      (by native_decide) (by native_decide)
    have h147' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreRootLowJumpdestPc [bytesStoreSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5, CS + 22, ?_⟩
      simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreSplitTgt] using h147
    obtain ⟨kJ, CJ, h147rd⟩ := h147'
    have h148 : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
        bytesStoreLowSplitPc [bytesStoreSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kJ + 1, CJ + 1, ?_⟩
      simpa [bytesStoreLowSplitPc, bytesStoreRootLowJumpdestPc] using
        h147rd.jumpdest (by native_decide) (by simp)
    obtain ⟨kL, CL, hlow⟩ := h148
    by_cases hpivotL : UInt256.gt (armSelNat bytesStoreBytecode bytesStoreLowSplitPc)
        (bytesStoreSelWord I) = ⟨0⟩
    · have h159 := RD.selectorSplitNotTakenAuto hlow bytesStoreLowSplitWellFormed hpivotL
        (by native_decide)
      have h159' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLowFallthroughFirstArmPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kL + 5, CL + 22, ?_⟩
        simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitNextPc] using h159
      obtain ⟨k159, C159, h159rd⟩ := h159'
      have h203 := h159rd
        |>.selectorArmNotTakenAuto (bytesStoreLowFallthroughArmsWellFormed 0 (by omega))
            (heqLowFallthrough0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLowFallthroughArmsWellFormed 1 (by omega))
            (heqLowFallthrough0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLowFallthroughArmsWellFormed 2 (by omega))
            (heqLowFallthrough0 2 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLowFallthroughArmsWellFormed 3 (by omega))
            (heqLowFallthrough0 3 (by omega)) (by native_decide)
      have h203rd : RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨203⟩ [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k159 + 5 + 5 + 5 + 5) (C159 + 22 + 22 + 22 + 22) := by
        change RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreBytecode bytesStoreLowFallthroughFirstArmPc 4)
          [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k159 + 5 + 5 + 5 + 5) (C159 + 22 + 22 + 22 + 22) at h203
        simpa [bytesStoreLowFallthroughArmsEnd] using h203
      exact h203rd.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have h206 := RD.selectorSplitTakenAuto hlow bytesStoreLowSplitWellFormed hpivotL
        (by native_decide) (by native_decide)
      have h206' : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLowTakenJumpdestPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kL + 5, CL + 22, ?_⟩
        simpa [bytesStoreSelWord, solcSelectorWord, bytesStoreLowSplitTgt] using h206
      obtain ⟨kJ2, CJ2, h206rd⟩ := h206'
      have h207 : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          bytesStoreLowTakenFirstArmPc [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine ⟨kJ2 + 1, CJ2 + 1, ?_⟩
        simpa [bytesStoreLowTakenFirstArmPc, bytesStoreLowTakenJumpdestPc] using
          h206rd.jumpdest (by native_decide) (by simp)
      obtain ⟨k207, C207, h207rd⟩ := h207
      have h240 := h207rd
        |>.selectorArmNotTakenAuto (bytesStoreLowTakenArmsWellFormed 0 (by omega))
            (heqLowTaken0 0 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLowTakenArmsWellFormed 1 (by omega))
            (heqLowTaken0 1 (by omega)) (by native_decide)
        |>.selectorArmNotTakenAuto (bytesStoreLowTakenArmsWellFormed 2 (by omega))
            (heqLowTaken0 2 (by omega)) (by native_decide)
      have h240rd : RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨240⟩ [bytesStoreSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k207 + 5 + 5 + 5) (C207 + 22 + 22 + 22) := by
        change RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I)
          (nthArmPc bytesStoreBytecode bytesStoreLowTakenFirstArmPc 3)
          [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k207 + 5 + 5 + 5) (C207 + 22 + 22 + 22) at h240
        simpa [bytesStoreLowTakenArmsEnd] using h240
      have h241 := h240rd.jumpdest (by native_decide) (by simp)
      exact h241.revertStub (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 15 → (bytesStoreSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases hwv : I.weiValue = ⟨0⟩
    · exact (bytesStoreX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
        |>.reEquivNoDispatch hcode (bytesStoreDispatch_none_nomatch hnm)
    · exact (bytesStoreX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv)
        |>.reEquivNoDispatch hcode (bytesStoreDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact bytesStoreShortRevert hcode hshort

/-! ## EVM and Solm body facts -/

def packetTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

theorem packetTagWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    packetTagWord σ_evm I = packetTagWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩

def bytesStoreSetByteIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreSetByteValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreFullPanicSelectorWord : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def bytesStoreFullPanic22Mem1 : ByteArray :=
  bytesStoreFullPanicSelectorWord.toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def bytesStoreFullPanic22Mem : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 bytesStoreFullPanic22Mem1 4 32

noncomputable def bytesStoreFullPanic22Mem1From (mem : ByteArray) : ByteArray :=
  bytesStoreFullPanicSelectorWord.toByteArray.write 0 mem 0 32

noncomputable def bytesStoreFullPanic22MemFrom (mem : ByteArray) : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 (bytesStoreFullPanic22Mem1From mem) 4 32

noncomputable def bytesStoreFullPanicMemFrom (code : UInt256) (mem : ByteArray) : ByteArray :=
  code.toByteArray.write 0 (bytesStoreFullPanic22Mem1From mem) 4 32

noncomputable abbrev currentLengthZeroAllocMem : ByteArray :=
  StringStoreLite.currentLengthZeroAllocMem

noncomputable abbrev currentLengthZeroMem : ByteArray :=
  StringStoreLite.currentLengthZeroMem

noncomputable abbrev currentLengthZeroReturnMem : ByteArray :=
  StringStoreLite.currentLengthZeroReturnMem

def currentLengthAllocSize (len : UInt256) : UInt256 :=
  StringStoreLite.currentLengthAllocSize len

def currentLengthFreePtr (len : UInt256) : UInt256 :=
  StringStoreLite.currentLengthFreePtr len

noncomputable abbrev currentLengthAllocMem (len : UInt256) : ByteArray :=
  StringStoreLite.currentLengthAllocMem len

noncomputable abbrev currentLengthMem (len : UInt256) : ByteArray :=
  StringStoreLite.currentLengthMem len

def currentLengthPayloadWord (header : UInt256) : UInt256 :=
  StringStoreLite.currentLengthPayloadWord header

noncomputable abbrev currentLengthPayloadMem (len header : UInt256) : ByteArray :=
  StringStoreLite.currentLengthPayloadMem len header

noncomputable abbrev currentLengthPayloadReturnMem (len header : UInt256) : ByteArray :=
  StringStoreLite.currentLengthPayloadReturnMem len header

theorem currentLengthZeroMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact StringStoreLite.currentLengthZeroMem_mload128

theorem currentLengthZeroMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact StringStoreLite.currentLengthZeroMem_mload64

theorem currentLengthZeroReturnMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact StringStoreLite.currentLengthZeroReturnMem_mload64

theorem currentLengthZeroReturnMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact StringStoreLite.currentLengthZeroReturnMem_mload128

theorem currentLengthZeroReturnMem_read160 :
    currentLengthZeroReturnMem.readWithPadding 160 32 = UInt256.toByteArray ⟨0⟩ := by
  exact StringStoreLite.currentLengthZeroReturnMem_read160

theorem currentLengthPayloadMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
  exact StringStoreLite.currentLengthPayloadMem_mload64 len header freePtr hfree

theorem currentLengthPayloadMem_mload128 (len header : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        len := by
  exact StringStoreLite.currentLengthPayloadMem_mload128 len header

theorem currentLengthPayloadReturnMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadReturnMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadReturnMem len header).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact StringStoreLite.currentLengthPayloadReturnMem_mload64 len header freePtr hfree

theorem currentLengthPayloadReturnMem_read192 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  exact StringStoreLite.currentLengthPayloadReturnMem_read192 len header

theorem currentLength_short_valid_lt32 {len : UInt256}
    (hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len.toNat < 32 :=
  StringStoreLite.currentLength_short_valid_lt32 hvalid0

theorem currentLength_notGt31_of_lt32 {len : UInt256} (hlt32 : len.toNat < 32) :
    UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
  StringStoreLite.currentLength_notGt31_of_lt32 hlt32

theorem bytesStore_shiftLeft_one_eq_mul_two_of_short {len : UInt256}
    (_hshort : len.toNat < 32) :
    UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
  show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
  rw [Nat.shiftLeft_eq]

theorem bytesStore_shiftLeft_three_eq_mul_eight_of_short {len : UInt256}
    (_hshort : len.toNat < 32) :
    UInt256.shiftLeft len ⟨3⟩ = UInt256.mul len ⟨8⟩ := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨3⟩ : UInt256).val ≥ 256)]
  show (len.toNat <<< 3) % UInt256.size = (len.toNat * 8) % UInt256.size
  rw [Nat.shiftLeft_eq]

theorem bytesStore_nat_land_248_shiftLeft_three_mod_size (n : Nat) :
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

theorem bytesStore_optimizedLongTailMaskShift_eq_core (len : UInt256) :
    UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩) =
      UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩) := by
  apply u256_inj
  rw [u256_land_toNat, u256_mul_toNat, StringStoreLite.u256_land_31_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨3⟩ : UInt256).val ≥ 256)]
  change Nat.land 248 ((len.toNat <<< 3) % UInt256.size) % UInt256.size =
    (8 * (len.toNat % 32)) % UInt256.size
  rw [bytesStore_nat_land_248_shiftLeft_three_mod_size]

theorem bytesStoreOptimizedLongTailMaskedWord_eq_core (word len : UInt256) :
    UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
          (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))))
      word =
      StringStoreLite.longDataTailMaskedWord word len := by
  rw [bytesStore_optimizedLongTailMaskShift_eq_core]
  unfold StringStoreLite.longDataTailMaskedWord
  rw [u256_land_comm]

theorem bytesStoreOptimizedShortStoredWord_eq_setShortPackedHeader
    (payloadWord len : UInt256) (hshort : len.toNat < 32) :
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord) =
      StringStoreLite.setShortPackedHeader payloadWord len := by
  rw [StringStoreLite.setShortPackedHeader]
  rw [bytesStore_shiftLeft_one_eq_mul_two_of_short hshort]
  rw [bytesStore_shiftLeft_three_eq_mul_eight_of_short hshort]
  rw [u256_mul_comm len ⟨2⟩]
  rw [u256_mul_comm len ⟨8⟩]
  rw [u256_land_comm
    (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len)))
    payloadWord]
  rw [u256_lor_comm]

theorem bytesStoreShortDecodedPayloadReadWithPadding_toList {I : ExecutionEnv}
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
    ((StringStoreLite.setDecodedValueBytes I).readWithPadding 0 32).toList =
      (I.calldata.toList.drop payloadStart.toNat).take len.toNat ++
        List.replicate (32 - len.toNat) 0 := by
  rw [StringStoreLite.setDecodedValueBytes_readWithPadding_short_toList
    (I := I)
    (by simpa [← hlenAbi] using hshort)
    (by simpa [← hlenAbi] using hnz)
    hpayload]
  rw [StringStoreLite.setDecodedValueBytes_eq_extract hlenAbi hpayloadStart hoffMax]
  rw [byteArray_toList_eq (I.calldata.extract payloadStart.toNat
    (payloadStart.toNat + len.toNat))]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq I.calldata]
  rw [show payloadStart.toNat + len.toNat - payloadStart.toNat = len.toNat by omega]
  rw [show (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat =
      len.toNat by rw [hlenAbi]]

theorem bytesStoreShortPayloadMaskedCallDataWord_eq_decodedWord {I : ExecutionEnv}
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
        ((StringStoreLite.setDecodedValueBytes I).readWithPadding 0 32) := by
  rw [StringStoreLite.setShortPackedHeader_mask_of_short hshort]
  rw [uInt256OfByteArray_readBytes_at_high_mask_eq_padded
    I.calldata payloadStart.toNat len.toNat hshort hsrc]
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq]
  rw [← byteArray_toList_eq
    ((StringStoreLite.setDecodedValueBytes I).readWithPadding 0 32)]
  rw [bytesStoreShortDecodedPayloadReadWithPadding_toList
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hpayload]
  rw [byteArray_toList_eq]

theorem bytesStoreOptimizedShortStoredWord_eq_solidityShortBytesWord {I : ExecutionEnv}
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
      solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I) := by
  rw [bytesStoreOptimizedShortStoredWord_eq_setShortPackedHeader
    (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)) len hshort]
  have hpayloadWord :=
    bytesStoreShortPayloadMaskedCallDataWord_eq_decodedWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload
  have hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat := by
    rw [StringStoreLite.setDecodedValueBytes_size hpayload]
    rw [hlenAbi]
  have htag :
      UInt256.mul ⟨2⟩ len =
        UInt256.ofNat ((StringStoreLite.setDecodedValueBytes I).size * 2) := by
    apply u256_inj
    rw [u256_mul_toNat]
    change (2 * len.toNat) % UInt256.size =
      ((StringStoreLite.setDecodedValueBytes I).size * 2) % UInt256.size
    rw [hsize, Nat.mul_comm]
  rw [StringStoreLite.setShortPackedHeader,
    solidityShortBytesWord]
  rw [hpayloadWord]
  rw [htag]

abbrev bytesStoreOptimizedShortStoredWord
    (I : ExecutionEnv) (len payloadStart : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
    (UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
      (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))

theorem bytesStoreOptimizedShortStoredWord_abbrev_eq_solidityShortBytesWord
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
    bytesStoreOptimizedShortStoredWord I len payloadStart =
      solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I) := by
  exact bytesStoreOptimizedShortStoredWord_eq_solidityShortBytesWord
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload

theorem bytesStoreSetHelperShortStoredWord_eq_solidityShortBytesWord
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
          (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart)) =
      solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I) := by
  rw [bytesStoreOptimizedShortStoredWord_eq_setShortPackedHeader
    (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart) len hshort]
  exact StringStoreLite.setShortPackedHeader_eq_solidityShortBytesWord
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload

theorem bytesStoreSetDecodedShortReturnEquiv {I : ExecutionEnv} {len : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    returnEquiv (UInt256.toByteArray len)
      (some (.int (StringStoreLite.setDecodedValueBytes I).size))
      setTransition.returnType := by
  have hlenSize : len.toNat = (StringStoreLite.setDecodedValueBytes I).size := by
    rw [StringStoreLite.setDecodedValueBytes_size hpayload, hlenAbi]
  change returnEquiv (UInt256.toByteArray len)
    (some (.int (StringStoreLite.setDecodedValueBytes I).size))
    (some (.elem (.int (.uint ⟨256, by decide⟩))))
  rw [← hlenSize]
  exact returnEquiv_of_encode (uint256ReturnEncoding len)

theorem currentLengthFreePtr_eq_192_of_short_nonzero {len : UInt256}
    (hnonzero : len ≠ ⟨0⟩) (hlt32 : len.toNat < 32) :
    currentLengthFreePtr len = ⟨192⟩ :=
  StringStoreLite.currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32

theorem bytesStoreStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [uint256Loc] using storageLocLoad_uint256 evm slot

theorem bytesStoreCurrentLengthResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
  have hbase :
      (∅ : Store).get? currentRef.base = none := by
    simp [currentRef]
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := ∅ } evm currentRef =
          .ok ({ base := "current", steps := [] } : EvaledStorageRef) := by
    simpa [currentRef] using
      (evalStorageRef_base
        (cfg := bytesStoreConfig)
        (solm := { contract := bytesStoreContract, locals := ∅ })
        (evm := evm) (base := "current"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])

theorem bytesStoreCurrentResolveOfGetNone {evm : EVM.State} {locals : Store}
    (hbase : locals.get? currentRef.base = none) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := locals } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := locals } evm currentRef =
          .ok ({ base := "current", steps := [] } : EvaledStorageRef) := by
    simpa [currentRef] using
      (evalStorageRef_base
        (cfg := bytesStoreConfig)
        (evm := evm) (base := "current"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])

theorem bytesStoreChunksResolve (evm : EVM.State) :
    resolveDynamicArrayRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .bytes) := by
  have hresolve :
      resolveStorageRef? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
    have hbase :
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)).get? chunksRef.base = none := by
      simp [chunksRef, Std.HashMap.get?_eq_getElem?]
    have her :
        evalStorageRef bytesStoreConfig
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evm chunksRef =
            .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
      simpa [chunksRef] using
        (evalStorageRef_base
          (cfg := bytesStoreConfig)
          (evm := evm) (base := "chunks"))
    exact resolveStorageRef?_ok hbase her (by
      simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])
  exact resolveDynamicArrayRef?_ok_of_resolve hresolve

theorem bytesStoreChunksResolveValue (evm : EVM.State) (value : ByteArray) :
    resolveDynamicArrayRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .bytes) := by
  have hresolve :
      resolveStorageRef? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
    have hbase :
        ((∅ : Store).insert "value" (.bytes value)).get? chunksRef.base = none := by
      simp [chunksRef, Std.HashMap.get?_eq_getElem?]
    have her :
        evalStorageRef bytesStoreConfig
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evm chunksRef =
            .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
      simpa [chunksRef] using
        (evalStorageRef_base
          (cfg := bytesStoreConfig)
          (evm := evm) (base := "chunks"))
    exact resolveStorageRef?_ok hbase her (by
      simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])
  exact resolveDynamicArrayRef?_ok_of_resolve hresolve

theorem bytesStoreChunksStorageResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
  have hbase :
      ((∅ : Store).insert "value" (.bytes ByteArray.empty)).get? chunksRef.base = none := by
    simp [chunksRef, Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
    simpa [chunksRef] using
      (evalStorageRef_base
        (cfg := bytesStoreConfig)
        (evm := evm) (base := "chunks"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])

theorem bytesStoreChunksStorageResolveValue (evm : EVM.State) (value : ByteArray) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef =
        .ok ({ base := "chunks", steps := [] }, .dynamicArray .bytes) := by
  have hbase :
      ((∅ : Store).insert "value" (.bytes value)).get? chunksRef.base = none := by
    simp [chunksRef, Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef =
          .ok ({ base := "chunks", steps := [] } : EvaledStorageRef) := by
    simpa [chunksRef] using
      (evalStorageRef_base
        (cfg := bytesStoreConfig)
        (evm := evm) (base := "chunks"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreContract, storageDecls, bytesSt])

theorem bytesStoreChunksArrayLengthEval (evm : EVM.State) :
    evalExpr? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm (.arrayLength .storage chunksRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  rw [evalExpr?, bytesStoreChunksStorageResolve evm]
  simp only [readStorageArrayLength?, bytesStoreConfig, bytesStoreStorageLayout,
    solidityStorageLayout, bytesStoreLayout, EvalResult.bind, bind, pure, List.nil_append]
  rw [bytesStoreStorageLocLoad_uint256]

theorem bytesStoreChunksArrayLengthEvalValue (evm : EVM.State) (value : ByteArray) :
    evalExpr? bytesStoreConfig
      { contract := bytesStoreContract, locals := (∅ : Store).insert "value" (.bytes value) }
      evm (.arrayLength .storage chunksRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  rw [evalExpr?, bytesStoreChunksStorageResolveValue evm value]
  simp only [readStorageArrayLength?, bytesStoreConfig, bytesStoreStorageLayout,
    solidityStorageLayout, bytesStoreLayout, EvalResult.bind, bind, pure, List.nil_append]
  rw [bytesStoreStorageLocLoad_uint256]

theorem bytesStoreCurrentLengthBaseSlot {evm : EVM.State} :
    ∃ loc, bytesStoreLayout { base := "current", steps := [.length] } evm =
      some loc ∧ loc.slot = ⟨0⟩ := by
  refine ⟨bytesLikeLengthLoc ⟨0⟩ evm, ?_, by simp⟩
  simp [bytesStoreLayout]

theorem bytesStoreChunksLengthBaseSlot {evm : EVM.State} :
    ∃ loc, bytesStoreLayout { base := "chunks", steps := [.length] } evm =
      some loc ∧ loc.slot = ⟨1⟩ := by
  refine ⟨uint256Loc ⟨1⟩, ?_, by simp [uint256Loc]⟩
  simp [bytesStoreLayout]

theorem bytesStoreChunkElemLengthBaseSlot {evm : EVM.State} (oldLen : UInt256) :
    ∃ loc,
      bytesStoreLayout
          { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat)), .length] }
          evm =
        some loc ∧ loc.slot = chunksDataBase + oldLen := by
  have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
    not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
  refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
  simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
    hnonneg, u256_ofNat_toNat oldLen]

theorem bytesStoreWriteEmptyChunkAt {evm : EVM.State} (oldLen : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) ⟨0⟩) := by
  exact writeSolidityBytesEmptyFromZero
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload

theorem bytesStoreWriteEmptyChunkShortPacked {evm : EVM.State}
    (oldLen header len : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) ⟨0⟩) := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := ByteArray.empty)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    (by decide) hload hpacked hflag hlen hvalid
  simpa [hshortEmpty] using hwrite

theorem bytesStoreWriteChunkShortPacked {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreWriteChunkLongPacked {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreWriteChunkLongPackedAbsent {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hpacked : checkBytesPacked (chunksDataBase + oldLen) evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .ok evm := by
  exact writeSolidityBytesLongPackedAbsent
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hpacked hflag hlen hvalid hmissing

theorem bytesStoreWriteChunkLongFromLongPrepared {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
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
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hflag hlen hvalid

theorem bytesStoreWriteChunkShortFromLongPrepared {evm : EVM.State}
    (oldLen header len : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) 0
          ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm (chunksDataBase + oldLen) 0
          ((len.toNat + 31) / 32)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (len := len)
    (value := value)
    rfl (bytesStoreChunkElemLengthBaseSlot oldLen)
    hvalueSize hload hflag hlen hvalid

theorem bytesStoreWriteChunkMalformedLong {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload hflag hbad

theorem bytesStoreWriteChunkMalformedShort {evm : EVM.State}
    (oldLen header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] })
    (baseSlot := chunksDataBase + oldLen) (header := header) (value := value)
    rfl
    (by
      have hnonneg : ¬ ((oldLen.toNat : Int) < 0) :=
        not_lt_of_ge (Int.natCast_nonneg oldLen.toNat)
      refine ⟨bytesLikeLengthLoc (chunksDataBase + oldLen) evm, ?_, by simp⟩
      simp [bytesStoreLayout, chunksElemSlot?, nonnegativeIndexSlot?,
        hnonneg, u256_ofNat_toNat oldLen])
    hload hflag hbad

theorem bytesStoreWordOfIntOfNatEq (n : Nat) :
    EVM.wordOfInt (Int.ofNat n) = UInt256.ofNat n := by
  exact wordOfInt_ofNat_eq n

theorem bytesStoreStorageLocStore_uint256_nat
    (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat n)) := by
  exact storageLocStore_uint256_nat evm slot n

theorem bytesStoreStorageLocStore_uint256_addOne
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
    bytesStoreStorageLocStore_uint256_nat evm slot (oldLen.toNat + 1)

theorem bytesStorePushChunkEmptyPushArray_of_post_header {evm : EVM.State} (oldLen : UInt256)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreContract,
      locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes ByteArray.empty) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) ⟨0⟩) := by
    exact bytesStoreWriteEmptyChunkAt (evm := evmLen) oldLen
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
  rw [pushArray?, bytesStoreChunksResolve evm]
  simp only [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) ⟨0⟩)
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStorePushChunkEmptyPushArray_of_ne {evm : EVM.State} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  exact bytesStorePushChunkEmptyPushArray_of_post_header (evm := evm) oldLen hloadLen
    (bytesStoreEmptyChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen hne hloadElem)

theorem bytesStorePushChunkMalformedLongPushArray_of_post_header {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) = .revert := by
    exact bytesStoreWriteChunkMalformedLong (evm := evmLen)
      oldLen header value
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hbad
  rw [pushArray?, bytesStoreChunksResolveValue evm value]
  simp only [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  exact hwrite

theorem bytesStorePushChunkMalformedLongPushArray_of_ne {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  exact bytesStorePushChunkMalformedLongPushArray_of_post_header (evm := evm)
    oldLen header value hloadLen
    (bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hbad

theorem bytesStorePushChunkMalformedShortPushArray_of_post_header {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) = .revert := by
    exact bytesStoreWriteChunkMalformedShort (evm := evmLen)
      oldLen header value
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hbad
  rw [pushArray?, bytesStoreChunksResolveValue evm value]
  simp only [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  exact hwrite

theorem bytesStorePushChunkMalformedShortPushArray_of_ne {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) = .revert := by
  exact bytesStorePushChunkMalformedShortPushArray_of_post_header (evm := evm)
    oldLen header value hloadLen
    (bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hbad

theorem bytesStorePushChunkEmptyPushArrayShortPacked_of_post_header {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreContract,
      locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hpackedLen : checkBytesPacked (chunksDataBase + oldLen) evmLen = true :=
    checkBytesPacked_of_storageLoad_land_one_zero
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag
  have hwrite :
      writeStorage? bytesStoreConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes ByteArray.empty) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) ⟨0⟩) := by
    exact bytesStoreWriteEmptyChunkShortPacked (evm := evmLen)
      oldLen header len
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
      hpackedLen hflag hlen hvalid
  rw [pushArray?, bytesStoreChunksResolve evm]
  simp only [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes ByteArray.empty) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) ⟨0⟩)
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStorePushChunkEmptyPushArrayShortPacked_of_ne {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
      evm chunksRef (some (.bytes ByteArray.empty)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) ⟨0⟩) := by
  exact bytesStorePushChunkEmptyPushArrayShortPacked_of_post_header (evm := evm)
    oldLen header len hloadLen
    (bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStorePushChunkShortPushArray_of_post_header {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
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
    rw [bytesStoreStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hpackedLen : checkBytesPacked (chunksDataBase + oldLen) evmLen = true :=
    checkBytesPacked_of_storageLoad_land_one_zero
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag
  have hwrite :
      writeStorage? bytesStoreConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evmLen evmLen.executionEnv.codeOwner
          (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
    exact bytesStoreWriteChunkShortPacked (evm := evmLen)
      oldLen header oldBytesLen value hvalueSize
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
      hpackedLen hflag hlen hvalid
  rw [pushArray?, bytesStoreChunksResolveValue evm value]
  simp only [bytesStoreConfig, bytesStoreStorageLayout, solidityStorageLayout,
    bytesStoreLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
    .ok (Solm.EVM.storageStore evmLen evm.executionEnv.codeOwner
      (chunksDataBase + oldLen) (solidityShortBytesWord value))
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv]

theorem bytesStorePushChunkShortPushArray_of_ne {evm : EVM.State}
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
    pushArray? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen)
        (solidityShortBytesWord value)) := by
  exact bytesStorePushChunkShortPushArray_of_post_header (evm := evm)
    oldLen header oldBytesLen value hvalueSize hloadLen
    (bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStorePushChunkEmptyBodyReturns {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm chunksRef (some (.bytes ByteArray.empty)) = .ok evm') :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evm'
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes ByteArray.empty)
  let solm0 : Frame := { contract := bytesStoreContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreConfig solm0 evm (.var "value") =
        .ok (.bytes ByteArray.empty) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreConfig solm0 evm' (.arrayLength .storage chunksRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    simpa [solm0, locals0] using bytesStoreChunksArrayLengthEval evm'
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.pushVal hvalue (by simpa [solm0, locals0] using hpush)) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStorePushChunkBodyReturns {evm evm' : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef (some (.bytes value)) = .ok evm') :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm'
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreConfig solm0 evm (.var "value") =
        .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreConfig solm0 evm' (.arrayLength .storage chunksRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    simpa [solm0, locals0] using bytesStoreChunksArrayLengthEvalValue evm' value
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.pushVal hvalue (by simpa [solm0, locals0] using hpush)) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStorePushChunkBodyRevertsOfPush {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm chunksRef (some (.bytes value)) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreContract, locals := locals0 }
  have hvalue :
      evalExpr? bytesStoreConfig solm0 evm (.var "value") =
        .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.pushValStoreRevert hvalue (by simpa [solm0, locals0] using hpush))

theorem bytesStorePushChunkEmptyFlagOfZero_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ I ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩)) = ⟨0⟩) :
    UInt256.land
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
      ⟨1⟩ = ⟨0⟩ := by
  rw [bytesStorePushChunkHeaderAfterLengthStoreZero_of_ne
    (oldLen := bytesStoreChunksLengthWord σ I) hne hzero]
  native_decide

theorem bytesStorePushChunkEmptyValidOfZero_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ I ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩)) = ⟨0⟩) :
    UInt256.sub
        (UInt256.land
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
          ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
  rw [bytesStorePushChunkHeaderAfterLengthStoreZero_of_ne
    (oldLen := bytesStoreChunksLengthWord σ I) hne hzero]
  native_decide

theorem bytesStoreDeleteCurrentShortZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    deleteStorage? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreContract, locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hresolve :
      resolveStorageRef? bytesStoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm] using
      bytesStoreCurrentResolveOfGetNone
        (evm := evm) (locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact deleteSolidityBytesShortZero
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) rfl hresolve bytesStoreCurrentLengthBaseSlot hload

theorem bytesStoreDeleteCurrentShortPacked {evm : EVM.State}
    {header len : UInt256} {copy : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "copy" (.bytes copy) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreContract, locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hresolve :
      resolveStorageRef? bytesStoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm] using
      bytesStoreCurrentResolveOfGetNone
        (evm := evm) (locals := (∅ : Store).insert "copy" (.bytes copy))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact deleteSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl hresolve bytesStoreCurrentLengthBaseSlot hload hpacked hflag hlen hvalid

theorem bytesStoreReadCurrentShortPackedExists {evm : EVM.State}
    {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray,
      evalExpr? bytesStoreConfig { contract := bytesStoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy) ∧ copy.size = len.toNat := by
  exact evalSolidityBytesShortPackedExists
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (solm := { contract := bytesStoreContract, locals := ∅ })
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl (bytesStoreCurrentLengthResolve evm) bytesStoreCurrentLengthBaseSlot
    hload hflag hlen hvalid

theorem bytesStoreWriteCurrentLongPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨0⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreWriteCurrentLongPackedAbsent {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evm := by
  exact writeSolidityBytesLongPackedAbsent
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid hmissing

theorem bytesStoreWriteCurrentLongFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
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
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreWriteCurrentShortPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreWriteCurrentShortFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 ((len.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0
            ((len.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨0⟩ (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreWriteCurrentMalformedLong {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hload hflag hbad

theorem bytesStoreWriteCurrentMalformedShort {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl bytesStoreCurrentLengthBaseSlot hload hflag hbad

theorem bytesStoreSetDecodedValueBytes_size_lt32 {I : ExecutionEnv} {len : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32) :
    (StringStoreLite.setDecodedValueBytes I).size < 32 := by
  rw [StringStoreLite.setDecodedValueBytes_size hpayload]
  simpa [hlenAbi] using hshort

theorem bytesStoreSetDecodedLength_le_solcMaxU64 {I : ExecutionEnv}
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
      ABI.solcMaxU64 :=
  Nat.le_of_not_gt hlenMax

theorem bytesStoreSetDecodedPayloadSource {I : ExecutionEnv}
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩).toNat +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
      I.calldata.size := by
  rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
  exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload

theorem bytesStoreWriteCurrentDecodedShortPacked
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes (StringStoreLite.setDecodedValueBytes I)) =
        .ok (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩
          (solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I))) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hvalueSize : (StringStoreLite.setDecodedValueBytes I).size < 32 :=
    bytesStoreSetDecodedValueBytes_size_lt32 hlenAbi hpayload hshort
  have hwrite := bytesStoreWriteCurrentShortPacked (evm := evmSolm0)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := StringStoreLite.setDecodedValueBytes I)
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0] using hwrite

theorem bytesStoreWriteCurrentEmptyShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
    writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := bytesStoreWriteCurrentShortPacked (evm := evmSolm0)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := ByteArray.empty)
    (by decide) hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, hshortEmpty] using hwrite

theorem bytesStoreWriteCurrentDecodedShortFromLongPrepared
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let oldLen : UInt256 := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
    writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes (StringStoreLite.setDecodedValueBytes I)) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0
            ((oldLen.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨0⟩ (solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I))) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hvalueSize : (StringStoreLite.setDecodedValueBytes I).size < 32 :=
    bytesStoreSetDecodedValueBytes_size_lt32 hlenAbi hpayload hshort
  have hwrite := bytesStoreWriteCurrentShortFromLongPrepared (evm := evmSolm0)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen)
    (value := StringStoreLite.setDecodedValueBytes I)
    hvalueSize hload hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, oldLen] using hwrite

theorem bytesStoreWriteCurrentMalformedLongOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreWriteCurrentMalformedLong
    (evm := evmSolm0) (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreWriteCurrentMalformedShortOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreWriteCurrentMalformedShort
    (evm := evmSolm0) (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreAssignCurrentOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwrite : writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    assignStorageRef? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
      evm .storage currentRef (.bytes value) =
        .ok
          ({ contract := bytesStoreContract,
             locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
               (.bytes value) },
           evmCurrent) := by
  have hresolve :
      resolveStorageRef? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
            (.bytes value) }
        evm currentRef = .ok ({ base := "current", steps := [] }, .bytes) := by
    exact bytesStoreCurrentResolveOfGetNone
      (evm := evm)
      (locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value))
      (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreSetBodyReturns {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignCurrent :
      assignStorageRef? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evm .storage currentRef (.bytes value) =
          .ok ({ contract := bytesStoreContract,
                 locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) },
              evmCurrent)) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreConfig solm1 evmCurrent (.arrayLength .localVar { base := "copy" }) =
        .ok (.int value.size) := by
    simp [solm1, locals1, locals0, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consNormal
          (ExecStmt.assign hcopy (by simpa [solm1, locals1, locals0] using hassignCurrent)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetBodyReturnsOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  exact bytesStoreSetBodyReturns (evm := evm) (evmCurrent := evmCurrent) (value := value)
    hwv (bytesStoreAssignCurrentOfWrite hwrite)

theorem bytesStoreSetBodyRevertsOfWrite {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body .reverted := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hresolve :
      resolveStorageRef? bytesStoreConfig solm1 evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simpa [solm1, locals1, locals0] using
      bytesStoreCurrentResolveOfGetNone
        (evm := evm)
        (locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value))
        (by simp [currentRef, Std.HashMap.get?_eq_getElem?])
  have hassign :
      assignStorageRef? bytesStoreConfig solm1 evm .storage currentRef (.bytes value) =
        .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consRevert (ExecStmt.assignStoreRevert hcopy hassign)

theorem bytesStoreSetRuntimeOfWriteAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmCurrent.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmCurrent.accountMap)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreSetBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

theorem bytesStoreSetRuntimeOfWriteEVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmEvm evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmEvm.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmEvm.accountMap)
    (hState : EVMStateEquiv evmEvm evmCurrent)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreSetBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
    hCreated hAccounts hState henc

theorem bytesStoreSetRuntimeOfWriteRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value : ByteArray}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .revert) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreSetBodyRevertsOfWrite
    (evm := evmSolm0) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreCurrentLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreCurrentLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ currentLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreCurrentLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreContract, locals := ∅ } evm (some (.int n))) :=
  bytesStoreCurrentLengthBodyReturns hwv (bytesStoreCurrentLengthResolve evm) hlen

theorem bytesStoreCurrentLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ currentLengthGetter.body
      .reverted :=
  bytesStoreCurrentLengthBodyReverts hwv (bytesStoreCurrentLengthResolve evm) hlen

theorem bytesStoreClearCurrentBodyRevertsOfRead {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ clearCurrentTransition.body
      .reverted := by
  have hresolve := bytesStoreCurrentLengthResolve evm
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.letDeclRevert (by
        have hdecode :
            solidityDecodeBytesLengthHeader
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) = .revert :=
          solidityDecodeBytesLengthHeader_revert_of_readStorageBytesLength_revert
            (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
            (er := { base := "current" }) (evm := evm)
            (baseSlot := ⟨0⟩)
            (header := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            rfl bytesStoreCurrentLengthBaseSlot rfl hlen
        exact evalSolidityBytesRevertOfDecodeRevert
          (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
          (solm := { contract := bytesStoreContract, locals := ∅ })
          (evm := evm) (ref := currentRef) (er := { base := "current" })
          (baseSlot := ⟨0⟩)
          (header := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          rfl hresolve bytesStoreCurrentLengthBaseSlot rfl hdecode)))

theorem bytesStoreClearCurrentBodyReturnsZero {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreConfig { contract := bytesStoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes ByteArray.empty))
    (hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm' (some (.int 0))) := by
  let solm1 : Frame :=
    { contract := bytesStoreContract,
      locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hret :
      evalExpr? bytesStoreConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int 0) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreClearCurrentBodyReturnsBytes {evm evm' : EVM.State} {copy : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreConfig { contract := bytesStoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy))
    (hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm' (some (.int copy.size))) := by
  let solm1 : Frame :=
    { contract := bytesStoreContract,
      locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hret :
      evalExpr? bytesStoreConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int copy.size) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStorePacketLengthResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes) := by
  have hbase :
      (∅ : Store).get? packetDataRef.base = none := by
    simp [packetDataRef]
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := ∅ } evm packetDataRef =
          .ok ({ base := "packet", steps := [.field "data"] } : EvaledStorageRef) := by
    simpa [packetDataRef] using
      (evalStorageRef_field
        (cfg := bytesStoreConfig)
        (solm := { contract := bytesStoreContract, locals := ∅ })
        (evm := evm) (base := "packet") (field := "data"))
  exact resolveStorageRef?_ok hbase her (by
    simp [storageTypeAt?, bytesStoreContract, storageDecls, packetStructDecl,
      packetStructTy, bytesSt, storageTypeStep?])

theorem bytesStorePacketLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        { base := "packet", steps := [.field "data"] } = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ packetLengthGetter.body
      (.returned { contract := bytesStoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStorePacketLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := ∅ } evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ packetLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStorePacketLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        { base := "packet", steps := [.field "data"] } = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ packetLengthGetter.body
      (.returned { contract := bytesStoreContract, locals := ∅ } evm (some (.int n))) :=
  bytesStorePacketLengthBodyReturns hwv (bytesStorePacketLengthResolve evm) hlen

theorem bytesStorePacketLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        { base := "packet", steps := [.field "data"] } = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm ∅ packetLengthGetter.body
      .reverted :=
  bytesStorePacketLengthBodyReverts hwv (bytesStorePacketLengthResolve evm) hlen

def bytesStoreMappedLengthLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))

def bytesStoreChunkLengthLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat))

def bytesStoreSetByteLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "index"
    (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat))).insert "value"
    (.int (Int.ofNat (bytesStoreSetByteValueWord I).toNat))

theorem bytesStoreSetByteLocals_get_index (I : ExecutionEnv) :
    (bytesStoreSetByteLocals I).get? "index" =
      some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
  rw [bytesStoreSetByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_self]

theorem bytesStoreSetByteLocals_getElem_index (I : ExecutionEnv) :
    (bytesStoreSetByteLocals I)["index"]? =
      some (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using bytesStoreSetByteLocals_get_index I

theorem bytesStoreSetByteLocals_get_current_none (I : ExecutionEnv) :
    (bytesStoreSetByteLocals I).get? "current" = none := by
  rw [bytesStoreSetByteLocals]
  rw [store_get_ne (h := by decide)]
  rw [store_get_ne (h := by decide)]
  simp

theorem bytesStoreSetByteLocals_getElem_current_none (I : ExecutionEnv) :
    (bytesStoreSetByteLocals I)["current"]? = none := by
  simpa [Std.HashMap.get?_eq_getElem?] using bytesStoreSetByteLocals_get_current_none I

theorem bytesStoreMappedLengthResolve (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreMappedLengthRef I, .bytes) := by
  have hbase :
      (bytesStoreMappedLengthLocals I).get? "mapped" = none := by
    simp [bytesStoreMappedLengthLocals]
  have hgetKey :
      (bytesStoreMappedLengthLocals I).get? "key" =
        some (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat)) := by
    simp [bytesStoreMappedLengthLocals]
  have her :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
        evm (mappedRef (.var "key")) =
          .ok (bytesStoreMappedLengthRef I) := by
    exact evalStorageRef_mindex_var_of_get?
      (base := "mapped") hgetKey (by simp [valueToKey?])
  exact resolveStorageRef?_ok hbase her (by
    simp [bytesStoreMappedLengthRef, storageTypeAt?, bytesStoreContract,
      storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreChunkLengthArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage "chunks" []
      (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) = .ok () := by
  simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreStorageLayout,
    solidityStorageLayout, bytesStoreLayout, bytesStoreContract, storageDecls, bytesSt,
    bytesStoreStorageLocLoad_uint256, hbound]

theorem bytesStoreChunkLengthArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage "chunks" []
      (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) = .revert := by
  have hle :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (bytesStoreChunkLengthIndexWord I).toNat :=
    Nat.le_of_not_gt hbound
  simp [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig, bytesStoreStorageLayout,
    solidityStorageLayout, bytesStoreLayout, bytesStoreContract, storageDecls, bytesSt,
    bytesStoreStorageLocLoad_uint256, hle]

theorem bytesStoreChunkLengthEvalStorageRef_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalStorageRef bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .ok (bytesStoreChunkLengthRef I) := by
  have hgetIndex :
      (bytesStoreChunkLengthLocals I).get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) := by
    simp [bytesStoreChunkLengthLocals]
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage "chunks" []
        (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) = .ok () :=
    bytesStoreChunkLengthArrayIndexInBounds_ok evm I hbound
  simpa [chunkRef, bytesStoreChunkLengthRef] using
    (evalStorageRef_aindex_var_of_get?_ok
      (cfg := bytesStoreConfig)
      (solm := { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I })
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreChunkLengthEvalStorageRef_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalStorageRef bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreChunkLengthLocals I).get? "chunkIndex" =
        some (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) := by
    simp [bytesStoreChunkLengthLocals]
  have hkey :
      valueToKey? (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) =
        some (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm bytesStoreContract.storage "chunks" []
        (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat)) = .revert :=
    bytesStoreChunkLengthArrayIndexInBounds_revert evm I hbound
  simpa [chunkRef] using
    (evalStorageRef_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig)
      (solm := { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I })
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreChunkLengthResolve (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreChunkLengthRef I, .bytes) := by
  have hbase :
      (bytesStoreChunkLengthLocals I).get? "chunks" = none := by
    simp [bytesStoreChunkLengthLocals]
  exact resolveStorageRef?_ok hbase
    (bytesStoreChunkLengthEvalStorageRef_ok evm I hbound)
    (by
      simp [bytesStoreChunkLengthRef, storageTypeAt?, bytesStoreContract,
        storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreChunkLengthResolveReverts (evm : EVM.State) (I : ExecutionEnv)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
      resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreChunkLengthLocals I).get? "chunks" = none := by
    simp [bytesStoreChunkLengthLocals]
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks
    (bytesStoreChunkLengthEvalStorageRef_revert evm I hbound)

theorem bytesStoreMappedLengthBodyReturns {evm : EVM.State} {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreMappedLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreMappedLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreMappedLengthLocals I) mappedLengthGetter.body
      (.returned
        { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
        evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreMappedLengthBodyReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
      evm (mappedRef (.var "key")) =
        .ok (bytesStoreMappedLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreMappedLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreMappedLengthLocals I) mappedLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreMappedLengthBodyReturnsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreMappedLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreMappedLengthLocals I) mappedLengthGetter.body
      (.returned
        { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
        evm (some (.int n))) :=
  bytesStoreMappedLengthBodyReturns hwv (bytesStoreMappedLengthResolve evm I) hlen

theorem bytesStoreMappedLengthBodyRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreMappedLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreMappedLengthLocals I) mappedLengthGetter.body .reverted :=
  bytesStoreMappedLengthBodyReverts hwv (bytesStoreMappedLengthResolve evm I) hlen

theorem bytesStoreChunkLengthBodyReturns {evm : EVM.State} {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreChunkLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreChunkLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body
      (.returned
        { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
        evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem bytesStoreChunkLengthBodyReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreChunkLengthRef I, .bytes))
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreChunkLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem bytesStoreChunkLengthBodyBoundsReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreConfig
      { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
      evm (chunkRef (.var "chunkIndex")) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, EvalResult.bind, bind])))

theorem bytesStoreChunkLengthBodyReturnsOfLength {evm : EVM.State}
    {I : ExecutionEnv} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreChunkLengthRef I) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body
      (.returned
        { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
        evm (some (.int n))) :=
  bytesStoreChunkLengthBodyReturns hwv
    (bytesStoreChunkLengthResolve evm I hbound) hlen

theorem bytesStoreChunkLengthBodyRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hlen : readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreChunkLengthRef I) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted :=
  bytesStoreChunkLengthBodyReverts hwv
    (bytesStoreChunkLengthResolve evm I hbound) hlen

theorem bytesStoreChunkLengthBodyBoundsRevertsOfLength {evm : EVM.State}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted :=
  bytesStoreChunkLengthBodyBoundsReverts hwv
    (bytesStoreChunkLengthResolveReverts evm I hbound)

theorem bytesStorePacketTagBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "packet" = none) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm locals packetTagGetter.body
      (.returned { contract := bytesStoreContract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef bytesStoreConfig
          { contract := bytesStoreContract, locals := locals } evm packetTagRef =
          .ok { base := "packet", steps := [.field "tag"] } := by
        simpa [packetTagRef] using
          (evalStorageRef_field
            (cfg := bytesStoreConfig)
            (solm := { contract := bytesStoreContract, locals := locals })
            (evm := evm) (base := "packet") (field := "tag"))
      have hty : storageTypeAt? bytesStoreContract.storage
          ({ base := "packet", steps := [.field "tag"] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      have hloc : (bytesStoreConfig.storage.layout
          { base := "packet", steps := [.field "tag"] }) =
          fun _ => some (uint256Loc ⟨3⟩) := by
        funext evm'
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
        (hty := hty) (hloc := hloc)]
      rw [bytesStoreStorageLocLoad_uint256])

theorem bytesStoreX_returnWord263 {cA gh bl σ σ₀ A I} {g : Sat256} {val : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [val, bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
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

noncomputable def bytesStoreReturnFromMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem bytesStoreReturnFromMem_size (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (bytesStoreReturnFromMem mem val).size = 160 := by
  unfold bytesStoreReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    show (USize.ofNat (128 - mem.size)).toNat = 32 from by
      rw [hsize]
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size, hsize]

theorem bytesStoreReturnFromMem_read64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (bytesStoreReturnFromMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold bytesStoreReturnFromMem
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

theorem bytesStoreReturnFromMem_mload64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bytesStoreReturnFromMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((bytesStoreReturnFromMem mem val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [bytesStoreReturnFromMem_size mem val hsize]; decide)
    (by decide)
    (bytesStoreReturnFromMem_read64 mem val hsize hread64)

theorem bytesStoreReturnFromMem_read128 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (bytesStoreReturnFromMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [bytesStoreReturnFromMem_size mem val hsize])]
  unfold bytesStoreReturnFromMem
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

theorem bytesStoreWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

theorem bytesStoreX_returnWord263OfMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [val, bytesStoreSelWord I] mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (bytesStoreReturnFromMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreReturnFromMem_mload64 mem val hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreReturnFromMem_read128 mem val hsize])
      (by evm_ov)]

theorem bytesStoreX_returnWord263OfMemState {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {val : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [val, bytesStoreSelWord I] mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (bytesStoreReturnFromMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (bytesStoreReturnFromMem_mload64 mem val hsize hread64)
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          bytesStoreReturnFromMem_read128 mem val hsize])
      (by evm_ov)]

theorem bytesStoreX_packetTag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (packetTagWord σ I)) := by
  obtain ⟨_, _, rd433⟩ := hreach
  have rd437 := evm_run rd433 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd438₀⟩ := rd437.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd438⟩ :
      ∃ k C, RD bytesStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨437⟩
        [packetTagWord σ I, bytesStoreSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [packetTagWord, initState] using rd438₀⟩
  have rd263 := evm_run rd438 with [
    push2 ⟨263⟩, jump (by native_decide)]
  exact bytesStoreX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreX_currentLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreCurrentLengthHeaderWord σ I, ⟨1393⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd441⟩ := hreach
  have rd1380 := evm_run rd441 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1380⟩, jump (by native_decide)]
  have rd1384 := evm_run rd1380 with [
    jumpdest, push0, push0, dup1]
  obtain ⟨_, _, rd1385₀⟩ := rd1384.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1385⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1385⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1385₀⟩
  exact ⟨_, _, evm_run rd1385 with [
    push2 ⟨1393⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_clearCurrentReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreCurrentLengthHeaderWord σ I, ⟨1413⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd449⟩ := hreach
  have rd1399 := evm_run rd449 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1399⟩, jump (by native_decide)]
  have rd1404 := evm_run rd1399 with [
    jumpdest, push0, push0, push0, dup1]
  obtain ⟨_, _, rd1405₀⟩ := rd1404.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1405⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1405₀⟩
  exact ⟨_, _, evm_run rd1405 with [
    push2 ⟨1413⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_packetLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStorePacketLengthHeaderWord σ I, ⟨1393⟩, ⟨2⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd476⟩ := hreach
  have rd1628 := evm_run rd476 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨1628⟩, jump (by native_decide)]
  have rd1635 := evm_run rd1628 with [
    jumpdest, push0, push1 ⟨2⟩, push0, add, dup1]
  obtain ⟨_, _, rd1636₀⟩ := rd1635.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1636⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1636⟩
        [bytesStorePacketLengthHeaderWord σ I, ⟨2⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStorePacketLengthHeaderWord, initState] using rd1636₀⟩
  exact ⟨_, _, evm_run rd1636 with [
    push2 ⟨1393⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStore_shiftRight_one_eq_div_two (w : UInt256) :
    UInt256.shiftRight w ⟨1⟩ = UInt256.div w ⟨2⟩ := by
  apply u256_inj
  simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Nat.shiftRight_eq_div_pow]
  norm_num [UInt256.size]

theorem bytesStore_shiftRight_five_eq_div_thirtyTwo (w : UInt256) :
    UInt256.shiftRight w ⟨5⟩ = UInt256.div w ⟨32⟩ := by
  apply u256_inj
  simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Nat.shiftRight_eq_div_pow]
  norm_num [UInt256.size]

theorem bytesStoreX_bytesLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreX_bytesLengthDecoderLongValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreX_bytesLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreX_bytesLengthDecoderShortValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreX_currentLengthMalformedPanic {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 bytesStoreFullPanic22Mem1 (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 bytesStoreFullPanic22Mem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_malformedPanicMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanic22MemFrom mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_malformedPanicMem6 {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanic22MemFrom mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_malformedPanicMemCarried {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2277⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanic22MemFrom mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_setShortNonemptyMalformedPanic {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {stk : List UInt256}
    (_hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2277⟩ stk
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty
      (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2277⟩ := hreach
  have hawGe : 5 ≤ (StringStoreLite.setHelperEntryAw len).toNat :=
    StringStoreLite.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2289₀ := evm_run rd2277 with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2289 := rd2289₀
  rw [hsel] at rd2289
  exact evm_run rd2289 with [
    raw mstore 0
      (bytesStoreFullPanic22Mem1From
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [StringStoreLite.set_mstoreCostSpec
          (aw := StringStoreLite.setHelperEntryAw len) (off := ⟨0⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (StringStoreLite.setHelperEntryAw len).toNat 0 32)) -
            Cₘ (StringStoreLite.setHelperEntryAw len) = 0
        rw [StringStoreLite.set_activeWordsMstore0_eq_self
          (aw := StringStoreLite.setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (StringStoreLite.set_activeWordsMstore0_eq_self
        (aw := StringStoreLite.setHelperEntryAw len) (by omega))
      (by omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0
      (bytesStoreFullPanic22MemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [StringStoreLite.set_mstoreCostSpec
          (aw := StringStoreLite.setHelperEntryAw len) (off := ⟨4⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (StringStoreLite.setHelperEntryAw len).toNat 4 32)) -
            Cₘ (StringStoreLite.setHelperEntryAw len) = 0
        rw [StringStoreLite.set_activeWordsMstore4_eq_self
          (aw := StringStoreLite.setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (StringStoreLite.set_activeWordsMstore4_eq_self
        (aw := StringStoreLite.setHelperEntryAw len) (by omega))
      (by omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide)
      (by
        intro s haw' hstk
        rw [StringStoreLite.set_revertCostSpec
          (aw := StringStoreLite.setHelperEntryAw len) (off := ⟨0⟩)
          (len := ⟨36⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat
            (MachineState.M (StringStoreLite.setHelperEntryAw len).toNat 0 36)) -
            Cₘ (StringStoreLite.setHelperEntryAw len) = 0
        rw [StringStoreLite.set_activeWordsRevert0_36_eq_self
          (aw := StringStoreLite.setHelperEntryAw len) (by omega)]
        simp)
      (by omega)]

theorem bytesStoreX_panic32Mem {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_bytesLengthDecoderLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_currentLengthMalformedPanic ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderLongMalformedMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMem ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderLongMalformedMemCarried
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMemCarried ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_currentLengthMalformedPanic ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderShortMalformedMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMem ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderShortMalformedMemCarried
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMemCarried ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderLongMalformedMem6 {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMem6 ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderShortMalformedMem6 {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_malformedPanicMem6 ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_currentLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderLongValid
    (bytesStoreX_currentLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_currentLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderShortValid
    (bytesStoreX_currentLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_currentLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1393⟩ := hdecoded
  have rd263 := evm_run rd1393 with [
    jumpdest, swap3, swap2, pop, pop, jump (by native_decide)]
  exact bytesStoreX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreX_currentLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreX_currentLengthReturnFromDecoded
    (bytesStoreX_currentLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreX_currentLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreX_currentLengthReturnFromDecoded
    (bytesStoreX_currentLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreX_currentLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformed
    (bytesStoreX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_currentLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨441⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformed
    (bytesStoreX_currentLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_clearCurrentLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformed
    (bytesStoreX_clearCurrentReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_clearCurrentShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformed
    (bytesStoreX_clearCurrentReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_clearCurrentZeroReachCopyDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreCurrentLengthHeaderWord σ I, ⟨1457⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1449₀⟩
  exact ⟨_, _, evm_run rd1449 with [
    push2 ⟨1457⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_clearCurrentZeroReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreCurrentLengthHeaderWord σ I, ⟨1457⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMem
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1457₀⟩ := hdecoded
  obtain ⟨_, _, rd1457⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
        [⟨0⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨263⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_clearCurrentDeleteShortZero {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [⟨0⟩, bytesStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd1732⟩ := hreach
  have rd1735pre := evm_run rd1732 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd1736₀⟩ := rd1735pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1736⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1736₀⟩
  have hdecode := bytesStoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1736 with [
      push2 ⟨1744⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1744⟩)
    (rest := [⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hflag
    hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1744₀⟩ := hdecode
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1744₀⟩
  have rd1748pre := evm_run rd1744 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd1748₀⟩ := rd1748pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1748⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1748⟩
        [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd1748₀⟩
  have rd1756 := evm_run rd1748 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1759⟩]
  have rd1756' := rd1756.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1555 := evm_run rd1756' with [pop, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd1555 with [jumpdest, pop, swap1, jump (by native_decide)]⟩

theorem bytesStoreX_clearCurrentZeroReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [⟨0⟩, bytesStoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
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

theorem bytesStoreX_clearCurrentShortZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  have hdecoded₀ := bytesStoreX_bytesLengthDecoderShortValid
    (hreach := bytesStoreX_clearCurrentReachDecoder hreach)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1413⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I])
    hflag
    hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1413₀⟩ := hdecoded₀
  have hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd1413₀⟩
  have hcopy := bytesStoreX_clearCurrentZeroReachCopyDecoder hdecoded
  have hdelStart := bytesStoreX_clearCurrentZeroReachDelete hcopy
    hflag hvalid hzero
  exact bytesStoreX_clearCurrentZeroReturnFromWrapper
    (bytesStoreX_clearCurrentDeleteShortZero hperm hdelStart hflag hvalid hzero)

theorem bytesStoreX_clearCurrentShortReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      (currentLengthPayloadMem len (bytesStoreCurrentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  have hvalidHeader :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded₀ := bytesStoreX_bytesLengthDecoderShortValid
    (hreach := bytesStoreX_clearCurrentReachDecoder hreach)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1413⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I])
    hflag hvalidHeader (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1413₀⟩ := hdecoded₀
  obtain ⟨_, _, rd1413⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1449₀⟩
  have hdecode := bytesStoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1449 with [
      push2 ⟨1457⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1457⟩)
    (rest := [⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1457₀⟩ := hdecode
  obtain ⟨_, _, rd1457⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
          bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1478⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨256⟩, ⟨256⟩, len, ⟨0⟩, ⟨160⟩, len,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1478₀⟩
  have rd1482 := evm_run rd1478 with [
    div, mul, dup4,
    raw mstore 3 (currentLengthPayloadMem len (bytesStoreCurrentLengthHeaderWord σ I))
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
      (currentLengthPayloadMem_mload128 len (bytesStoreCurrentLengthHeaderWord σ I))
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [hfree] using
      (evm_run rd1532 with [
        swap2, pop, push0, push0, push2 ⟨1555⟩, swap2, swap1, push2 ⟨1732⟩,
        jump (by native_decide)])⟩

theorem bytesStoreX_clearCurrentDeleteShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I]
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd1732⟩ := hreach
  have rd1735pre := evm_run rd1732 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd1736₀⟩ := rd1735pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1736⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩,
          bytesStoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1736₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecode := bytesStoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1736 with [
      push2 ⟨1744⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1744⟩)
    (rest := [⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I])
    (mem := mem) (aw := aw) (rdata := rdata)
    hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1744₀⟩ := hdecode
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1744₀⟩
  have rd1748pre := evm_run rd1744 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd1748₀⟩ := rd1748pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1748⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1748⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_clearCurrentShortReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I]
      (currentLengthPayloadMem len (bytesStoreCurrentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C)
    (hfree : currentLengthFreePtr len = ⟨192⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (currentLengthPayloadMem_mload64 len (bytesStoreCurrentLengthHeaderWord σ I) ⟨192⟩ hfree)
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 3 (currentLengthPayloadReturnMem len (bytesStoreCurrentLengthHeaderWord σ I))
      (UInt256.ofNat 7) (by native_decide)
      mem_cost
      (by rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost
      (currentLengthPayloadReturnMem_mload64 len (bytesStoreCurrentLengthHeaderWord σ I)
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

theorem bytesStoreX_clearCurrentShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have hdelStart := bytesStoreX_clearCurrentShortReachDelete
    (g := g) hreach hflag hlen hvalid hnonzero
  have hdel := bytesStoreX_clearCurrentDeleteShortValid
    (g := g) hperm hdelStart hflag hlen hvalid
  exact bytesStoreX_clearCurrentShortReturnFromWrapper hdel hfree

theorem bytesStoreX_packetLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩, ⟨2⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderLongValid
    (bytesStoreX_packetLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_packetLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨2⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderShortValid
    (bytesStoreX_packetLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_packetLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [len, ⟨2⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1393⟩ := hdecoded
  have rd263 := evm_run rd1393 with [
    jumpdest, swap3, swap2, pop, pop, jump (by native_decide)]
  exact bytesStoreX_returnWord263 ⟨_, _, rd263⟩

theorem bytesStoreX_packetLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreX_packetLengthReturnFromDecoded
    (bytesStoreX_packetLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreX_packetLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreX_packetLengthReturnFromDecoded
    (bytesStoreX_packetLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreX_packetLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformed
    (bytesStoreX_packetLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_packetLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨476⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformed
    (bytesStoreX_packetLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_mappedLengthDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
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
      bytesStoreMappedLengthKeyWord I from rfl] at rd390
  exact ⟨_, _, evm_run rd390 with [
    jumpdest, push2 ⟨1113⟩, jump (by native_decide)]⟩

theorem bytesStoreX_mappedLengthDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_mappedLengthDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨376⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_chunkLengthDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
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
      bytesStoreChunkLengthIndexWord I from rfl] at rd517
  exact ⟨_, _, evm_run rd517 with [
    jumpdest, push2 ⟨1693⟩, jump (by native_decide)]⟩

theorem bytesStoreX_chunkLengthDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_chunkLengthDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨503⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_pushChunkDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_pushChunkDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_setDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
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

theorem bytesStoreX_setDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
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
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
        exact hstartPlus31Small
    · apply StringStoreLite.slt_zero_of_left_low_right_high
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
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

theorem bytesStoreX_setDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
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

theorem bytesStoreX_setDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
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

theorem bytesStoreX_pushChunkDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_pushChunkDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
        omega
    · apply StringStoreLite.slt_zero_of_left_low_right_high
      · rw [StringStoreLite.setStartPlus31_toNat I.calldata hoffMax]
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

theorem bytesStoreX_pushChunkDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_pushChunkDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
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

theorem bytesStoreX_pushChunkDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨457⟩ [bytesStoreSelWord I]
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
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨263⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_setDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetDecoder
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

theorem bytesStoreX_setReachStorageWriteMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2388⟩
        [⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)
        (StringStoreLite.setHelperEntryAw len)
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
    raw mstore 0 (StringStoreLite.currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        rfl)
      (by decide) (by evm_ov),
    dup1, swap4, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (StringStoreLite.currentLengthMem len) (UInt256.ofNat 5)
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
    (StringStoreLite.setCalldataMem I.calldata len payloadStart)
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
    (StringStoreLite.setPaddedMem I.calldata len payloadStart)
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
    simpa [StringStoreLite.setCalldataMem, StringStoreLite.setPaddedMem,
      StringStoreLite.setHelperEntryAw, awCopy, awPad,
      StringStoreLite.currentLengthAllocSize, StringStoreLite.currentLengthFreePtr]
      using rd2388⟩

theorem bytesStoreX_setReachWriteHeaderDecoderNonempty {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [StringStoreLite.currentLengthHeaderWord σ I, ⟨2428⟩, len, ⟨2434⟩, len,
        ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2388⟩ := bytesStoreX_setReachStorageWriteMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach
  have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    simpa [ABI.solcMaxU64] using hlenMax
  have rd2391 := evm_run rd2388 with [
    jumpdest, dup2,
    raw mload 0 len (StringStoreLite.setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [StringStoreLite.set_activeWordsMload128_eq_self
          (StringStoreLite.setHelperEntryAw_ge5_of_u64 hlenMax)]
        simp)
      (StringStoreLite.setPaddedMem_mload128_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (StringStoreLite.set_activeWordsMload128_eq_self
        (StringStoreLite.setHelperEntryAw_ge5_of_u64 hlenMax))
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
        [StringStoreLite.currentLengthHeaderWord σ I, ⟨2428⟩, len, ⟨2434⟩, len,
          ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I]
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)
        (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [StringStoreLite.currentLengthHeaderWord, initState] using rd2423₀⟩
  exact ⟨_, _, evm_run rd2424 with [push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_pushChunkIncrementLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1573⟩
      [bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  obtain ⟨_, _, rd1559⟩ := hreach
  have rd1563pre := evm_run rd1559 with [jumpdest, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd1564₀⟩ := rd1563pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1564⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1564⟩
        [bytesStoreChunksLengthWord σ I, ⟨1⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreChunksLengthWord, initState] using rd1564₀⟩
  have rd1568pre := evm_run rd1564 with [dup1, dup3, add, dup3]
  obtain ⟨_, _, rd1569₀⟩ := rd1568pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1569⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1569⟩
        [bytesStoreChunksLengthWord σ I, ⟨1⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
    exact ⟨_, _, by
      simpa [initState, u256_add_comm (bytesStoreChunksLengthWord σ I) (⟨1⟩ : UInt256)]
        using rd1569₀⟩
  exact ⟨_, _, evm_run rd1569 with [
    push0, swap2, dup3,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov)]⟩

private theorem bytesStoreX_pushChunkReachWriteHelper_literal {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {oldLen len payloadStart ret sel : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1573⟩
      [oldLen, ⟨0⟩, len, payloadStart, ret, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
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

private theorem bytesStoreX_pushChunkReachWriteHelperFromBody_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hinc := bytesStoreX_pushChunkIncrementLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreX_pushChunkReachWriteHelper_literal
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (oldLen := bytesStoreChunksLengthWord σ I) (len := len)
    (payloadStart := payloadStart) (ret := ⟨263⟩) (sel := bytesStoreSelWord I) hinc

theorem bytesStoreX_writeBytesHelperReachHeaderDecoder {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2599⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hov : tail.length + 9 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_bytesLengthDecoderShortValidMemCarried {cA gh bl σinit τ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

private theorem bytesStoreX_pushChunkReachWriteHeaderDecoder_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ ::
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
            UInt256) + bytesStoreChunksLengthWord σ I) ::
        payloadStart :: len :: ⟨1617⟩ ::
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
            UInt256) + bytesStoreChunksLengthWord σ I) ::
        ⟨0⟩ :: len :: payloadStart :: ⟨263⟩ :: bytesStoreSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hhelper := bytesStoreX_pushChunkReachWriteHelperFromBody_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_pushChunkReachWriteHeaderDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: (chunksDataBase + bytesStoreChunksLengthWord σ I) ::
        payloadStart :: len :: ⟨1617⟩ :: (chunksDataBase + bytesStoreChunksLengthWord σ I) ::
        ⟨0⟩ :: len :: payloadStart :: ⟨263⟩ :: bytesStoreSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  simpa [bytesStoreChunksDataBaseLiteral] using
    bytesStoreX_pushChunkReachWriteHeaderDecoder_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax

theorem bytesStoreX_setReachWriteHeaderDecoderEmpty {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [StringStoreLite.currentLengthHeaderWord σ I, ⟨2428⟩, ⟨0⟩, ⟨2434⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2388₀⟩ := bytesStoreX_setReachStorageWriteMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := (⟨0⟩ : UInt256)) (payloadStart := payloadStart) hreach
  obtain ⟨_, _, rd2388⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2388⟩
        [⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
          ⟨263⟩, bytesStoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [currentLengthZeroReturnMem, StringStoreLite.currentLengthZeroReturnMem,
        StringStoreLite.setCalldataMem, StringStoreLite.setPaddedMem,
        StringStoreLite.setHelperEntryAw, StringStoreLite.currentLengthAllocSize,
        StringStoreLite.currentLengthFreePtr] using rd2388₀⟩
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
        [StringStoreLite.currentLengthHeaderWord σ I, ⟨2428⟩, ⟨0⟩, ⟨2434⟩,
          ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          payloadStart, ⟨263⟩, bytesStoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [StringStoreLite.currentLengthHeaderWord, initState] using rd2424₀⟩
  exact ⟨_, _, evm_run rd2424 with [push2 ⟨2246⟩, jump (by native_decide)]⟩

private theorem bytesStoreX_pushChunkLongMalformed_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                        UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_pushChunkReachWriteHeaderDecoder_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax
  exact bytesStoreX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (header :=
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩)))
    (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I,
      payloadStart, len, ⟨1617⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (by simpa using hdecoder)
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreX_pushChunkLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hflag
  have hbad' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                        UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hbad
  exact bytesStoreX_pushChunkLongMalformed_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag' hbad'

private theorem bytesStoreX_pushChunkShortMalformed_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_pushChunkReachWriteHeaderDecoder_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax
  exact bytesStoreX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (header :=
      ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩)))
    (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I,
      payloadStart, len, ⟨1617⟩,
      (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (by simpa using hdecoder)
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreX_pushChunkShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hflag
  have hbad' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hbad
  exact bytesStoreX_pushChunkShortMalformed_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag' hbad'

theorem bytesStoreX_writeBytesHelperShortHeaderReachCleanup {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
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
    ∃ k C, RD bytesStoreBytecode I g
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
  have hdecReach := bytesStoreX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata) hreach hlenMax
    (by omega)
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
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

theorem bytesStoreX_writeBytesCleanupOldShort {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_writeBytesCleanupOldLongNoClear {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_setCurrentCleanupOldLongShortToLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (⟨0⟩ :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hshort : UInt256.lt len ⟨32⟩ = ⟨1⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (⟨0⟩ ::
        UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩ ::
        (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ::
        ⟨0⟩ :: oldLen :: len :: ret :: tail)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentHashAw aw) rdata (cA, σ) k C := by
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
    raw mstore (Cₘ (StringStoreLite.clearCurrentBaseAw aw) - Cₘ aw)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (StringStoreLite.clearCurrentHashAw aw) -
        Cₘ (StringStoreLite.clearCurrentBaseAw aw))
      StringStoreLite.clearCurrentBaseWord
      (StringStoreLite.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentHashAw, StringStoreLite.clearCurrentBaseAw])
      (StringStoreLite.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov),
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

theorem bytesStoreX_setShortLongHeaderReachCleanupLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2359⟩
      [⟨0⟩, UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩,
        ⟨0⟩ + StringStoreLite.clearCurrentBaseWord, ⟨0⟩, oldLen, len, ⟨2434⟩,
        len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, σ) k C := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hvalidHeader :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)
        (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := StringStoreLite.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < oldLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldLen len = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := len) (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  exact bytesStoreX_setCurrentCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (oldLen := oldLen) (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setLongOldLongNoClearReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hvalidHeader :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)
        (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := StringStoreLite.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  exact bytesStoreX_writeBytesCleanupOldLongNoClear
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setClearDataWordsLoopDone {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx count = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_setClearDataWordsLoopStep {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx count) = ⟨0⟩)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_setClearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx count base dead₀ dead₁ dead₂ ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (idx :: count :: base :: dead₀ :: dead₁ :: dead₂ :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex idx i) count) =
        ⟨0⟩)
    (hdone : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex idx fuel) count = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [StringStoreLite.clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        bytesStoreX_setClearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
          (dead₀ := dead₀) (dead₁ := dead₁) (dead₂ := dead₂) (ret := ret)
          (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret hov
  | succ n ih =>
      have hstep := bytesStoreX_setClearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
        (dead₀ := dead₀) (dead₁ := dead₁) (dead₂ := dead₂) (ret := ret)
        (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by
          simpa [StringStoreLite.clearDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hstep' :
          ∃ k C, RD bytesStoreBytecode I g
            (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
            (((⟨1⟩ : UInt256) + idx) :: count :: base :: dead₀ :: dead₁ :: dead₂ ::
              ret :: rest)
            mem aw rdata (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
        simpa [u256_add_comm idx base] using hstep
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (StringStoreLite.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i)
              count) =
              ⟨0⟩ := by
        intro i hi
        simpa [StringStoreLite.clearDataWordsLoopIndex,
          StringStoreLite.clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.lt
            (StringStoreLite.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n)
            count =
            ⟨0⟩ := by
        simpa [StringStoreLite.clearDataWordsLoopIndex,
          StringStoreLite.clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep' hcontinueTail hdoneTail

theorem bytesStoreX_setShortLongHeaderReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩ fuel) k C := by
  have hloopEntry := bytesStoreX_setShortLongHeaderReachCleanupLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
    hreach hnz hshort hlenMax hsrc hflag holdLen hvalid
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := ⟨0⟩ + StringStoreLite.clearCurrentBaseWord)
    (dead₀ := (⟨0⟩ : UInt256)) (dead₁ := oldLen) (dead₂ := len)
    (ret := (⟨2434⟩ : UInt256))
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.clearCurrentBaseMemFrom
      (StringStoreLite.setPaddedMem I.calldata len payloadStart))
    (aw := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hloop

theorem bytesStoreX_setShortLongHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_setShortLongHeaderReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
      (fuel := count.toNat)
      hperm hreach hnz hshort hlenMax hsrc hflag holdLen hvalid hcontinue hdone

theorem bytesStoreX_setShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C := by
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428⟩ := hdecoded
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [oldLen] using
        (evm_run rd2428 with [jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)])⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  exact bytesStoreX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdNotLong (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2260 := rd2259.jumpiNT (by native_decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2260 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStore_shiftRight_one_eq_div_two] at rd2288
  have rd2277 := rd2288.jumpiNT (by native_decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd2277⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreX_setShortNonemptyLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  exact bytesStoreX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := hdecoder)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setShortNonemptyShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  exact bytesStoreX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := hdecoder)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setShortNonemptyLongMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hflag
  have hbadCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hbad
  exact bytesStoreX_setShortNonemptyLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflagCore hbadCore

theorem bytesStoreX_setShortNonemptyShortMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hflag
  have hbadCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hbad
  exact bytesStoreX_setShortNonemptyShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflagCore hbadCore

theorem bytesStoreSetShortNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart : UInt256} {value : ByteArray}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreX_setShortNonemptyLongMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hreach hnz hlenMax hsrc hflag hbad
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .revert := by
    have hwrite₀ := bytesStoreWriteCurrentMalformedLongOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    hcode hwv hrev hd hdec (by simpa [evmSolm0] using hwrite)

theorem bytesStoreSetShortNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart : UInt256} {value : ByteArray}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreX_setShortNonemptyShortMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hreach hnz hlenMax hsrc hflag hbad
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .revert := by
    have hwrite₀ := bytesStoreWriteCurrentMalformedShortOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    hcode hwv hrev hd hdec (by simpa [evmSolm0] using hwrite)

theorem bytesStoreSetDecodedNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreSelWord I]
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact bytesStoreSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    exact bytesStoreSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreSetShortNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd
    hdec
    (by simpa [len] using hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreSetDecodedNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreSelWord I]
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact bytesStoreSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    exact bytesStoreSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreSetShortNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd
    hdec
    (by simpa [len] using hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreSetRawDecodedNonemptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreSelWord I]
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  have hlenEvm :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenEvm]
    exact bytesStoreSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    rw [hlenEvm]
    dsimp [payloadStart]
    exact bytesStoreSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreSetShortNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd hdec
    (by rw [hlenEvm]; exact hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreSetRawDecodedNonemptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreSelWord I]
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  have hlenEvm :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setTransition.params.map Param.name)
        (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)) := by
    dsimp [value]
    exact decodeCalldata_set_some
      (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxLe : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenEvm]
    exact bytesStoreSetDecodedLength_le_solcMaxU64 hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    rw [hlenEvm]
    dsimp [payloadStart]
    exact bytesStoreSetDecodedPayloadSource hoffMax hlenWord hpayloadList
  exact bytesStoreSetShortNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (value := value)
    hcode hwv hAccounts
    (by simpa [len, payloadStart] using hreach)
    hd hdec
    (by rw [hlenEvm]; exact hnz)
    hlenMaxLe hsrc hflag hbad

theorem bytesStoreSetRawDecodedNonemptyLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hreach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  exact bytesStoreSetRawDecodedNonemptyLongMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsel hAccounts hreach
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    hnz hflag hbad

theorem bytesStoreSetRawDecodedNonemptyShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hreach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  exact bytesStoreSetRawDecodedNonemptyShortMalformedRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsel hAccounts hreach
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    hnz hflag hbad

theorem bytesStoreX_setShortNonemptyWriteHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      StringStoreLite.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperPayloadAw len)
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
    (Cₘ (StringStoreLite.setHelperPayloadAw len) -
      Cₘ (StringStoreLite.setHelperEntryAw len))
    (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart)
    (StringStoreLite.setHelperPayloadAw len)
    rd2460pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        StringStoreLite.setHelperPayloadAw, haddr])
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
    simpa [initState, StringStoreLite.setHelperPayloadWord,
      StringStoreLite.setHelperPayloadAw, List.append_assoc] using
      (evm_run rd2480₀ with [
        push2 ⟨2572⟩, jump (by native_decide),
        jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)])⟩

theorem bytesStoreX_setLongReachLoopFrom2434
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {len payloadStart : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [⟨0⟩, StringStoreLite.clearCurrentBaseWord,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          ⟨32⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom mem)
        (StringStoreLite.clearCurrentHashAw aw) rdata (cA, τ) k' C' := by
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
    raw mstore (Cₘ (StringStoreLite.clearCurrentBaseAw aw) - Cₘ aw)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup2,
    raw keccak256
      (Cₘ (StringStoreLite.clearCurrentHashAw aw) -
        Cₘ (StringStoreLite.clearCurrentBaseAw aw))
      StringStoreLite.clearCurrentBaseWord
      (StringStoreLite.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentHashAw, StringStoreLite.clearCurrentBaseAw])
      (StringStoreLite.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov),
    push1 ⟨31⟩, not, dup6, and, swap2]⟩

theorem bytesStoreX_setLongDataWordsLoopStep
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx cutoff) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [(⟨32⟩ : UInt256) + idx, (⟨1⟩ : UInt256) + slot, cutoff, gtFlag,
          (⟨32⟩ : UInt256) + stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2514⟩
        [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot word) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd2514₀⟩
  exact ⟨_, _, by
    simpa [u256_add_comm idx ⟨32⟩, u256_add_comm slot ⟨1⟩,
      u256_add_comm stride ⟨32⟩] using
      (evm_run rd2514 with [
        push1 ⟨32⟩, swap5, dup6, add, swap5, push1 ⟨1⟩, swap1,
        swap3, add, swap2, add, push2 ⟨2499⟩, jump (by native_decide)])⟩

theorem bytesStoreX_setLongDataWordsLoopGenerated
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + StringStoreLite.longDataWordsLoopStride stride i,
          StringStoreLite.longDataWordsLoopIndex idx i,
          StringStoreLite.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          StringStoreLite.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
        [StringStoreLite.longDataWordsLoopIndex idx fuel,
          StringStoreLite.longDataWordsLoopSlot slot fuel, cutoff, gtFlag,
          StringStoreLite.longDataWordsLoopStride stride fuel, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem (StringStoreLite.longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, StringStoreLite.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
        k' C' := by
  induction fuel generalizing idx slot stride aw τ with
  | zero =>
      simpa [StringStoreLite.longDataWordsLoopIndex,
        StringStoreLite.longDataWordsLoopSlot,
        StringStoreLite.longDataWordsLoopStride,
        StringStoreLite.longDataWordsLoopAw,
        StringStoreLite.longDataWordsForwardFrom] using hreach
  | succ n ih =>
      have hstep := bytesStoreX_setLongDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
        (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
        (payloadStart := payloadStart)
        (word := StringStoreLite.longDataWordsLoopWord mem aw ptr stride 0)
        (aw := aw)
        (awLoad := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
        hperm hreach
        (by
          simpa [StringStoreLite.longDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        (by
          intro s haw hstk
          simpa [StringStoreLite.longDataWordsLoopIndex,
            StringStoreLite.longDataWordsLoopSlot,
            StringStoreLite.longDataWordsLoopStride,
            StringStoreLite.longDataWordsLoopAw] using
            hmloadCost 0 (Nat.zero_lt_succ n) s haw hstk)
        (by simp [StringStoreLite.longDataWordsLoopWord,
          StringStoreLite.longDataWordsLoopStride,
          StringStoreLite.longDataWordsLoopAw])
        rfl
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (StringStoreLite.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i)
              cutoff) =
              ⟨0⟩ := by
        intro i hi
        simpa [StringStoreLite.longDataWordsLoopIndex,
          StringStoreLite.longDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hmloadCostTail : ∀ i, i < n → ∀ s : State,
          s.machineState.activeWords =
            StringStoreLite.longDataWordsLoopAw
              (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
              ptr ((⟨32⟩ : UInt256) + stride) i →
          s.machineState.stack =
            [ptr + StringStoreLite.longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i,
              StringStoreLite.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i,
              StringStoreLite.longDataWordsLoopSlot ((⟨1⟩ : UInt256) + slot) i,
              cutoff, gtFlag,
              StringStoreLite.longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i,
              len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
              ⟨263⟩, bytesStoreSelWord I] →
          memoryExpansionCost s .MLOAD = mloadCost := by
        intro i hi s haw hstk
        have haw' :
            s.machineState.activeWords =
              StringStoreLite.longDataWordsLoopAw aw ptr stride (i + 1) := by
          simpa [StringStoreLite.longDataWordsLoopAw_succ_base] using haw
        have hstk' :
            s.machineState.stack =
              [ptr + StringStoreLite.longDataWordsLoopStride stride (i + 1),
                StringStoreLite.longDataWordsLoopIndex idx (i + 1),
                StringStoreLite.longDataWordsLoopSlot slot (i + 1), cutoff, gtFlag,
                StringStoreLite.longDataWordsLoopStride stride (i + 1), len, ⟨0⟩,
                ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
                bytesStoreSelWord I] := by
          simpa [StringStoreLite.longDataWordsLoopIndex,
            StringStoreLite.longDataWordsLoopIndex_succ_base,
            StringStoreLite.longDataWordsLoopSlot_succ_base,
            StringStoreLite.longDataWordsLoopStride_succ_base,
            StringStoreLite.longDataWordsLoopStride] using hstk
        exact hmloadCost (i + 1) (Nat.succ_lt_succ hi) s haw' hstk'
      have htail := ih
        (idx := (⟨32⟩ : UInt256) + idx)
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        (aw := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (τ := sstoreAccountMap I.codeOwner τ slot
          (StringStoreLite.longDataWordsLoopWord mem aw ptr stride 0))
        hstep hcontinueTail hmloadCostTail
      simpa [StringStoreLite.longDataWordsForwardFrom,
        StringStoreLite.longDataWordsLoopIndex,
        StringStoreLite.longDataWordsLoopSlot,
        StringStoreLite.longDataWordsLoopStride,
        StringStoreLite.longDataWordsLoopAw,
        StringStoreLite.longDataWordsLoopIndex_succ_base,
        StringStoreLite.longDataWordsLoopSlot_succ_base,
        StringStoreLite.longDataWordsLoopStride_succ_base,
        StringStoreLite.longDataWordsLoopAw_succ_base,
        StringStoreLite.longDataWordsLoopWord_succ_base] using htail

theorem bytesStoreX_setLongDataWordsLoopDoneNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2572⟩
        [gtFlag, stride, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_setLongDataWordsLoopTailLoaded
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2545⟩
        [word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_setLongTailMaskShiftFromLoaded
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2545⟩
      [word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2552⟩
        [UInt256.shiftLeft len ⟨3⟩, UInt256.lnot ⟨0⟩, word, slot, cutoff,
          gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2552 := evm_run hreach with [
    push0, not, push1 ⟨3⟩, dup8, swap1, shl]
  have hpc :
      ({ val := 2545 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
          { val := 1 } + { val := 1 } + { val := 1 } : UInt256) =
        ⟨2552⟩ := by native_decide
  exact ⟨_, _, by
    simpa [hpc] using rd2552⟩

theorem bytesStoreX_setLongTailMaskAnd248
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2552⟩
      [UInt256.shiftLeft len ⟨3⟩, UInt256.lnot ⟨0⟩, word, slot, cutoff,
        gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2555⟩
        [UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩), UInt256.lnot ⟨0⟩,
          word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2555 := evm_run hreach with [push1 ⟨248⟩, and]
  have hpc : ({ val := 2552 } + UInt256.ofNat 2 + { val := 1 } : UInt256) =
      ⟨2555⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2555⟩

theorem bytesStoreX_setLongTailMaskShrNot
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2555⟩
      [UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩), UInt256.lnot ⟨0⟩,
        word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2557⟩
        [UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
            (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))),
          word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2557 := evm_run hreach with [shr, not]
  have hpc : ({ val := 2555 } + { val := 1 } + { val := 1 } : UInt256) =
      ⟨2557⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2557⟩

theorem bytesStoreX_setLongTailMaskFinal
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride len ptr ret payloadStart word mask aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2557⟩
      [mask, word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2559⟩
        [slot, UInt256.land mask word, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, τ) k' C' := by
  have rd2559 := evm_run hreach with [and, dup2]
  have hpc : ({ val := 2557 } + { val := 1 } + { val := 1 } : UInt256) =
      ⟨2559⟩ := by native_decide
  exact ⟨_, _, by simpa [hpc] using rd2559⟩

theorem bytesStoreX_setLongTailStoreFromMask
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot maskedWord cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2559⟩
      [slot, maskedWord, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2560⟩
        [slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot maskedWord) k' C' := by
  obtain ⟨_, _, rd2560₀⟩ := hreach.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc : ({ val := 2559 } + { val := 1 } : UInt256) = ⟨2560⟩ := by
    native_decide
  exact ⟨_, _, by simpa [hpc, sstoreAccountMap, initState] using rd2560₀⟩

theorem bytesStoreX_setLongDataWordsLoopDoneTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (StringStoreLite.longDataTailMaskedWord word len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloaded := bytesStoreX_setLongDataWordsLoopTailLoaded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (idx := idx) (slot := slot)
    (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (word := word)
    (aw := aw) (awLoad := awLoad) (mem := mem) (rdata := rdata)
    (mloadCost := mloadCost)
    hreach hdone htail hmloadCost hmload hawLoad
  obtain ⟨_, _, rd2545⟩ := hloaded
  have hshift := bytesStoreX_setLongTailMaskShiftFromLoaded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2545
  obtain ⟨_, _, rd2552⟩ := hshift
  have hand := bytesStoreX_setLongTailMaskAnd248
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2552
  obtain ⟨_, _, rd2555⟩ := hand
  have hmask := bytesStoreX_setLongTailMaskShrNot
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word) (aw := awLoad) (mem := mem)
    (rdata := rdata) rd2555
  obtain ⟨_, _, rd2557⟩ := hmask
  have hfinal := bytesStoreX_setLongTailMaskFinal
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (word := word)
    (mask := UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
        (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))))
    (aw := awLoad) (mem := mem) (rdata := rdata) rd2557
  obtain ⟨_, _, rd2559⟩ := hfinal
  have hstore := bytesStoreX_setLongTailStoreFromMask
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot)
    (maskedWord := StringStoreLite.longDataTailMaskedWord word len)
    (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (aw := awLoad)
    (mem := mem) (rdata := rdata) hperm
    (by simpa [bytesStoreOptimizedLongTailMaskedWord_eq_core] using rd2559)
  obtain ⟨_, _, rd2560⟩ := hstore
  have rd2571pre := evm_run rd2560 with [
    jumpdest, pop, pop, push1 ⟨1⟩, dup4, push1 ⟨1⟩, shl, add, dup5]
  obtain ⟨_, _, rd2572₀⟩ := rd2571pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2572⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2572⟩
        [gtFlag, stride, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (StringStoreLite.longDataTailMaskedWord word len))
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

theorem bytesStoreX_setLongDataWordsGeneratedTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw awTail wordTail : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + StringStoreLite.longDataWordsLoopStride stride i,
          StringStoreLite.longDataWordsLoopIndex idx i,
          StringStoreLite.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          StringStoreLite.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw aw ptr stride fuel →
      s.machineState.stack =
        [ptr + StringStoreLite.longDataWordsLoopStride stride fuel,
          StringStoreLite.longDataWordsLoopSlot slot fuel, cutoff, gtFlag,
          StringStoreLite.longDataWordsLoopStride stride fuel, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + StringStoreLite.longDataWordsLoopStride stride fuel).toNat ≥ mem.size ∨
          (ptr + StringStoreLite.longDataWordsLoopStride stride fuel) ≥
            StringStoreLite.longDataWordsLoopAw aw ptr stride fuel * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding
          (ptr + StringStoreLite.longDataWordsLoopStride stride fuel).toNat 32))) =
        wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (StringStoreLite.longDataWordsLoopAw aw ptr stride fuel).toNat
          (ptr + StringStoreLite.longDataWordsLoopStride stride fuel).toNat 32) = awTail)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
            (StringStoreLite.longDataWordsLoopSlot slot fuel)
            (StringStoreLite.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := bytesStoreX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (aw := aw) (mem := mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := loopMloadCost)
    hperm hreach hcontinue hloopMloadCost
  exact bytesStoreX_setLongDataWordsLoopDoneTail
    (σinit := σinit)
    (τ := StringStoreLite.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := StringStoreLite.longDataWordsLoopIndex idx fuel)
    (slot := StringStoreLite.longDataWordsLoopSlot slot fuel) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := StringStoreLite.longDataWordsLoopStride stride fuel)
    (len := len) (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
    (word := wordTail) (aw := StringStoreLite.longDataWordsLoopAw aw ptr stride fuel)
    (awLoad := awTail) (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
    hperm hloop hdone htail hmloadCost hmload hawTail hret

theorem bytesStoreX_setLongDataWordsGeneratedNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2499⟩
      [idx, slot, cutoff, gtFlag, stride, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + StringStoreLite.longDataWordsLoopStride stride i,
          StringStoreLite.longDataWordsLoopIndex idx i,
          StringStoreLite.longDataWordsLoopSlot slot i, cutoff, gtFlag,
          StringStoreLite.longDataWordsLoopStride stride i, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        mem (StringStoreLite.longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := bytesStoreX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (len := len) (ptr := ptr) (ret := ret)
    (payloadStart := payloadStart) (aw := aw) (mem := mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost)
    hperm hreach hcontinue hmloadCost
  exact bytesStoreX_setLongDataWordsLoopDoneNoTail
    (σinit := σinit)
    (τ := StringStoreLite.longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := StringStoreLite.longDataWordsLoopIndex idx fuel)
    (slot := StringStoreLite.longDataWordsLoopSlot slot fuel) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := StringStoreLite.longDataWordsLoopStride stride fuel)
    (len := len) (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
    (aw := StringStoreLite.longDataWordsLoopAw aw ptr stride fuel)
    (mem := mem) (rdata := rdata)
    hperm hloop hdone hnoTail hret

theorem bytesStoreX_setWriteLongFrom2434NoTailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (hnoTail : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i,
          StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i,
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom mem)
        (StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw aw)
            (StringStoreLite.clearCurrentBaseMemFrom mem) fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := bytesStoreX_setLongReachLoopFrom2434
    (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact bytesStoreX_setLongDataWordsGeneratedNoTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := StringStoreLite.clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (len := len) (ptr := (⟨128⟩ : UInt256))
    (ret := (⟨592⟩ : UInt256)) (payloadStart := payloadStart)
    (aw := StringStoreLite.clearCurrentHashAw aw)
    (mem := StringStoreLite.clearCurrentBaseMemFrom mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost)
    hperm hloopStart hcontinue hdone hnoTail hmloadCost (by native_decide)

theorem bytesStoreX_setWriteLongFrom2434TailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len wordTail awTail : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (htail :
      UInt256.isZero (UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i,
          StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i,
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel,
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord fuel,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel).toNat ≥
            (StringStoreLite.clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel) ≥
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((StringStoreLite.clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel).toNat 32))) =
        wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel).toNat
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ fuel).toNat 32) =
        awTail) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
              StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (StringStoreLite.clearCurrentHashAw aw)
              (StringStoreLite.clearCurrentBaseMemFrom mem) fuel)
            (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord fuel)
            (StringStoreLite.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := bytesStoreX_setLongReachLoopFrom2434
    (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact bytesStoreX_setLongDataWordsGeneratedTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := StringStoreLite.clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (len := len) (ptr := (⟨128⟩ : UInt256))
    (ret := (⟨592⟩ : UInt256)) (payloadStart := payloadStart)
    (aw := StringStoreLite.clearCurrentHashAw aw) (awTail := awTail)
    (wordTail := wordTail) (mem := StringStoreLite.clearCurrentBaseMemFrom mem)
    (rdata := rdata) (fuel := fuel) (mloadCost := mloadCost)
    (loopMloadCost := loopMloadCost)
    hperm hloopStart hcontinue hdone htail hloopMloadCost hmloadCost hmload hawTail
    (by native_decide)

theorem bytesStoreX_setWriteLongFrom2434NoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len aw : UInt256} {mem rdata : ByteArray}
    {k C mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hmloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i,
          StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i,
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom mem)
        (StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32))
        rdata
        (cA, sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw aw)
            (StringStoreLite.clearCurrentBaseMemFrom mem) (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact bytesStoreX_setWriteLongFrom2434NoTailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    hperm hlong hreach
    (fun i hi => StringStoreLite.longDataLoopContinue len hi)
    (StringStoreLite.longDataLoopDone len)
    (StringStoreLite.longDataNoTail len hnoTailMod)
    hmloadCost

theorem bytesStoreX_setWriteLongFrom2434Tail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len wordTail awTail aw : UInt256} {mem rdata : ByteArray}
    {k C mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C)
    (hloopMloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i,
          StringStoreLite.longDataWordsLoopIndex ⟨0⟩ i,
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ i, len, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32) →
      s.machineState.stack =
        [⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32),
          StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32),
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32), len,
          ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩,
          bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (StringStoreLite.clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩
              (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((StringStoreLite.clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) = wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩
            (len.toNat / 32)).toNat
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32) = awTail) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
              StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (StringStoreLite.clearCurrentHashAw aw)
              (StringStoreLite.clearCurrentBaseMemFrom mem) (len.toNat / 32))
            (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
              (len.toNat / 32))
            (StringStoreLite.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact bytesStoreX_setWriteLongFrom2434TailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (wordTail := wordTail) (awTail := awTail)
    (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    (loopMloadCost := loopMloadCost)
    hperm hlong hreach
    (fun i hi => StringStoreLite.longDataLoopContinue len hi)
    (StringStoreLite.longDataLoopDone len)
    (StringStoreLite.longDataTail len htailMod)
    hloopMloadCost hmloadCost hmload hawTail

theorem bytesStoreX_setWriteLongFrom2434NoTailAfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (StringStoreLite.setHelperEntryAw len).toNat := by
    have hge := StringStoreLite.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq :
      StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len) =
        StringStoreLite.setHelperEntryAw len :=
    StringStoreLite.clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (StringStoreLite.setPaddedMem I.calldata len payloadStart).size := by
    have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
      hnz hsrc (StringStoreLite.setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart)) =
        StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart) :=
    StringStoreLite.clearCurrentBaseMemFrom_idem hmemGe
  obtain ⟨k', C', rd⟩ :=
    bytesStoreX_setWriteLongFrom2434NoTail
      (payloadStart := payloadStart) (len := len)
      (aw := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (mem := StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong hnoTailMod hreach
      (by
        intro i hi s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [StringStoreLite.longDataWordsLoopAw, hcur] at hnext
        have hcurD :
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i =
              StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len)) := by
          simpa [hawEq] using hcur
        have hnextD :
            UInt256.ofNat
              (MachineState.M
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.clearCurrentHashAw
                    (StringStoreLite.setHelperEntryAw len))).toNat
                ((⟨128⟩ : UInt256) +
                  StringStoreLite.longDataWordsLoopStride ⟨32⟩ i).toNat 32) =
              StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len)) := by
          simpa [hawEq] using hnext
        rw [hcurD, hnextD])
  have hawLoop :
      StringStoreLite.longDataWordsLoopAw (StringStoreLite.setHelperEntryAw len)
          ⟨128⟩ ⟨32⟩ (len.toNat / 32) =
        StringStoreLite.setHelperEntryAw len := by
    simpa [hawEq] using
      StringStoreLite.longDataWordsLoopAw_setHelper_eq
        (len := len) hlenMax (len.toNat / 32) (by omega)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq, hawLoop] using rd

theorem bytesStoreX_setWriteLongFrom2434TailAfterClearBase
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
        (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0)))
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
              StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
              (StringStoreLite.clearCurrentBaseMemFrom
                (StringStoreLite.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
              (len.toNat / 32))
            (StringStoreLite.longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (StringStoreLite.setHelperEntryAw len).toNat := by
    have hge := StringStoreLite.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq :
      StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len) =
        StringStoreLite.setHelperEntryAw len :=
    StringStoreLite.clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (StringStoreLite.setPaddedMem I.calldata len payloadStart).size := by
    have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
      hnz hsrc (StringStoreLite.setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart)) =
        StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart) :=
    StringStoreLite.clearCurrentBaseMemFrom_idem hmemGe
  have hmloadTail :
      (if (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.clearCurrentBaseMemFrom
                (StringStoreLite.setPaddedMem I.calldata len payloadStart))).size ∨
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len)))
              ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))).readWithPadding
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) =
        wordTail := by
    simpa [hmemIdem, hawEq, hwordTail] using
      StringStoreLite.longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax
  obtain ⟨k', C', rd⟩ :=
    bytesStoreX_setWriteLongFrom2434Tail
      (payloadStart := payloadStart) (len := len) (wordTail := wordTail)
      (awTail := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (aw := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (mem := StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong htailMod hreach
      (by
        intro i hi s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [StringStoreLite.longDataWordsLoopAw, hcur] at hnext
        have hcurD :
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩ i =
              StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len)) := by
          simpa [hawEq] using hcur
        have hnextD :
            UInt256.ofNat
              (MachineState.M
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.clearCurrentHashAw
                    (StringStoreLite.setHelperEntryAw len))).toNat
                ((⟨128⟩ : UInt256) +
                  StringStoreLite.longDataWordsLoopStride ⟨32⟩ i).toNat 32) =
              StringStoreLite.clearCurrentHashAw
                (StringStoreLite.clearCurrentHashAw
                  (StringStoreLite.setHelperEntryAw len)) := by
          simpa [hawEq] using hnext
        rw [hcurD, hnextD])
      (by
        intro s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.clearCurrentHashAw
                (StringStoreLite.setHelperEntryAw len))) ⟨128⟩ ⟨32⟩
              (len.toNat / 32))
          (off := (⟨128⟩ : UInt256) +
            StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32))
          s haw hstk])
      hmloadTail
      (by
        simpa [hawEq] using
          StringStoreLite.longDataWordsLoopAw_setHelper_tail_mload_eq
            (len := len) hlenMax htailMod)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq] using rd

theorem bytesStoreX_setEmptyWriteZeroFrom2434
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2480⟩
        [(⟨0⟩ : UInt256).gt ⟨31⟩, ⟨32⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
          ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩,
          bytesStoreSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, hpacked0] using rd2480₀⟩
  exact ⟨_, _, evm_run rd2480 with [
    push2 ⟨2572⟩, jump (by native_decide),
    jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreX_setShortNonemptyWriteHeaderAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    let payloadWord : UInt256 :=
      StringStoreLite.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.setHelperPayloadAw len)
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
  have hawEntry : StringStoreLite.setHelperEntryAw len = ⟨7⟩ :=
    StringStoreLite.setHelperEntryAw_eq_7_of_short_nonzero hnz hshort
  have hawHash :
      StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len) =
        ⟨7⟩ := by
    rw [hawEntry]
    native_decide
  have hawPayload : StringStoreLite.setHelperPayloadAw len = ⟨7⟩ :=
    StringStoreLite.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have hclearSize :
      (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart)).size =
        (StringStoreLite.setPaddedMem I.calldata len payloadStart).size := by
    exact StringStoreLite.clearCurrentBaseMemFrom_size_of_ge32
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (by
        have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
          hnz hsrc (StringStoreLite.setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)
  have hread160 :
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)).readWithPadding
          160 32 =
        (StringStoreLite.setPaddedMem I.calldata len payloadStart).readWithPadding 160 32 :=
    StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_read160_short_nonzero
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
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart)).size
          ∨ (⟨160⟩ : UInt256) ≥
              StringStoreLite.clearCurrentHashAw
                (StringStoreLite.setHelperEntryAw len) * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart)).readWithPadding
                (⟨160⟩ : UInt256).toNat 32))) =
        StringStoreLite.setHelperPayloadWord I.calldata len payloadStart := by
    rw [if_neg]
    · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hread160]
      exact (StringStoreLite.setHelperPayloadWord_eq_mload160_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc).symm
    · apply not_or.mpr
      constructor
      · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hclearSize]
        have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
          hnz hsrc (StringStoreLite.setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · rw [hawHash]
        decide
  have rd2461₀ := RD.mload
    (Cₘ (StringStoreLite.setHelperPayloadAw len) -
      Cₘ (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len)))
    (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart)
    (StringStoreLite.setHelperPayloadAw len)
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
    simpa [initState, StringStoreLite.setHelperPayloadWord,
      StringStoreLite.setHelperPayloadAw, List.append_assoc] using
      (evm_run rd2480₀ with [
        push2 ⟨2572⟩, jump (by native_decide),
        jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)])⟩

theorem bytesStoreX_setShortNonemptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperPayloadAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have haw : StringStoreLite.setHelperPayloadAw len = ⟨7⟩ :=
    StringStoreLite.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
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
    raw mload 0 len (StringStoreLite.setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (StringStoreLite.setPaddedMem_mload128_short_nonzero_payloadAw
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (StringStoreLite.setHelperPayloadAw len)
      (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (StringStoreLite.setPaddedMem_mload64_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 (StringStoreLite.setShortReturnMem I.calldata len payloadStart)
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
      (StringStoreLite.setShortReturnMem_mload64 I.calldata len payloadStart hnz hshort hsrc)
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
          StringStoreLite.setShortReturnMem_read192 I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

theorem bytesStoreX_setEmptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
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
    raw mstore 0 StringStoreLite.setEmptyReturnMem (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      StringStoreLite.setEmptyReturnMem_mload64
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨160⟩) ⟨160⟩).toNat = 32 from by decide,
          StringStoreLite.setEmptyReturnMem_read160])
      (by evm_ov)]

theorem bytesStoreX_setEmptyReturnFromWriteLongMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      StringStoreLite.clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload128
      (by native_decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      StringStoreLite.clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 StringStoreLite.setEmptyReturnMemLong (UInt256.ofNat 6)
      (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      StringStoreLite.setEmptyReturnMemLong_mload64
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨160⟩) ⟨160⟩).toNat = 32 from by decide,
          StringStoreLite.setEmptyReturnMemLong_read160])
      (by evm_ov)]

theorem bytesStoreX_setLongReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have hentryGe5 : 5 ≤ (StringStoreLite.setHelperEntryAw len).toNat :=
    StringStoreLite.setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hentryGe1 : 1 ≤ (StringStoreLite.setHelperEntryAw len).toNat := by omega
  have hawEq :
      StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len) =
        StringStoreLite.setHelperEntryAw len :=
    StringStoreLite.clearCurrentHashAw_eq_self_of_ge1 hentryGe1
  have hentryGe3 : 3 ≤ (StringStoreLite.setHelperEntryAw len).toNat := by omega
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
    have hgtNat : 31 < len.toNat := by omega
    rw [ult_one (by simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using hgtNat)]
    decide
  have hfreeGe96 : 96 ≤ (currentLengthFreePtr len).toNat :=
    StringStoreLite.currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hfreeLeMem :
      (currentLengthFreePtr len).toNat ≤
        (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart)).size :=
    StringStoreLite.currentLengthFreePtr_le_clearCurrentBaseMemFrom_setPaddedMem_size_u64
      I.calldata len payloadStart hnz hlenMax hsrc
  have rd263 := evm_run rd592 with [
    jumpdest, pop,
    raw mload 0 len
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, StringStoreLite.set_activeWordsMload128_eq_self hentryGe5]
        omega)
      (StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_mload128_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact StringStoreLite.set_activeWordsMload128_eq_self hentryGe5)
      (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len)
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, StringStoreLite.activeWordsMload64_eq_self hentryGe3]
        omega)
      (StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_mload64_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact StringStoreLite.activeWordsMload64_eq_self hentryGe3)
      (by evm_ov),
    swap1, dup2]
  let returnMem := len.toByteArray.write 0
    (StringStoreLite.clearCurrentBaseMemFrom
      (StringStoreLite.setPaddedMem I.calldata len payloadStart))
    (currentLengthFreePtr len).toNat 32
  let awStore :=
    UInt256.ofNat
      (MachineState.M
        (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len)).toNat
        (currentLengthFreePtr len).toNat 32)
  have hawStore :
      UInt256.ofNat
        (MachineState.M
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len)).toNat
          (currentLengthFreePtr len).toNat 32) =
        awStore := rfl
  have rdStore := evm_run rd273 with [
    raw mstore
      (Cₘ awStore -
        Cₘ (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len)))
      returnMem awStore (by native_decide)
      (by
        intro s haw hstk
        simpa [awStore, returnMem] using
          (StringStoreLite.set_mstoreCostSpec
            (aw := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (off := currentLengthFreePtr len)
            (stk := [len, currentLengthFreePtr len, bytesStoreSelWord I]) s haw hstk))
      (by rfl)
      hawStore (by evm_ov),
    push1 ⟨32⟩, add]
  have hreturnRead64 :
      returnMem.readWithPadding 64 32 = UInt256.toByteArray (currentLengthFreePtr len) := by
    simpa [returnMem] using
      StringStoreLite.currentLengthReturnWrite_preserves_read64
        (mem := StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeGe96 hfreeLeMem
        (by
          rw [StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_read64_u64
            I.calldata len payloadStart hnz hlenMax hsrc]
          exact StringStoreLite.setPaddedMem_read64 I.calldata len payloadStart hnz hsrc
            (StringStoreLite.setDataEnd_toNat_of_u64 hlenMax))
  have hreturnSize64 : 64 < returnMem.size := by
    have hge := StringStoreLite.writeWord_size_gt64_of_mem
      (mem := StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (off := (currentLengthFreePtr len).toNat) (word := len)
      (by
        rw [StringStoreLite.clearCurrentBaseMemFrom_size_of_ge32]
        · have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
            hnz hsrc (StringStoreLite.setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega
        · have hsize := StringStoreLite.setPaddedMem_size I.calldata len payloadStart
            hnz hsrc (StringStoreLite.setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega)
      hfreeLeMem
    simpa [returnMem] using hge
  have hawStoreNoWrap :
      awStore.toNat * 32 < UInt256.size := by
    simpa [awStore, hawEq] using
      StringStoreLite.setHelperEntryAw_mstoreFreePtr_mul32_lt_u64
        (len := len) hnz hlenMax
  have hawStoreGe3 : 3 ≤ awStore.toNat := by
    simpa [awStore, hawEq] using
      StringStoreLite.setHelperEntryAw_mstoreFreePtr_ge3_u64 (len := len) hnz hlenMax
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
      (StringStoreLite.wordMul32_not_le64_of_ge3 hawStoreGe3 hawStoreNoWrap)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let awFinal := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) = awFinal := rfl
  have hretLen : (UInt256.sub (⟨32⟩ + currentLengthFreePtr len)
      (currentLengthFreePtr len)).toNat = 32 :=
    by
      simpa [u256_add_comm (⟨32⟩ : UInt256) (currentLengthFreePtr len)] using
        StringStoreLite.currentLengthFreePtr_retLen_of_len_lt_sign_pos
          (len := len) hlenLt (Nat.pos_of_ne_zero hnz)
  have hretBytes :
      returnMem.readWithPadding (currentLengthFreePtr len).toNat
        (UInt256.sub (⟨32⟩ + currentLengthFreePtr len) (currentLengthFreePtr len)).toNat =
        UInt256.toByteArray len := by
    rw [hretLen]
    simpa [returnMem] using
      StringStoreLite.currentLengthReturnWrite_readBack
        (mem := StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeLeMem
  exact evm_run rdStore with [
    jumpdest, push1 ⟨64⟩,
    raw mload
      (Cₘ awFinal - Cₘ awStore)
      (currentLengthFreePtr len) awFinal (by native_decide)
      (by
        intro s haw hstk
        simpa [awFinal] using
          (StringStoreLite.set_mloadCostSpec
            (aw := awStore) (off := (⟨64⟩ : UInt256))
            (stk := [currentLengthFreePtr len + ⟨32⟩, bytesStoreSelWord I])
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
          (StringStoreLite.returnCostSpec
            (aw := awFinal) (off := currentLengthFreePtr len)
            (len := UInt256.sub (⟨32⟩ + currentLengthFreePtr len)
              (currentLengthFreePtr len))
            (stk := [bytesStoreSelWord I]) s haw hstk))
      hretBytes
      (by evm_ov)]

theorem bytesStoreX_setEmptyShortHeaderWriteReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (payloadStart := payloadStart) hreach
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hdecoder hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428⟩ := hdecoded
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [oldLen] using
        (evm_run rd2428 with [jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)])⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  have hwriteReach := bytesStoreX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨0⟩) (oldLen := oldLen)
    (len := (⟨0⟩ : UInt256)) (ret := ⟨2434⟩)
    (tail := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hcleanupReach holdNotLong (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2434⟩ := hwriteReach
  have hwrite := bytesStoreX_setEmptyWriteZeroFrom2434
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (payloadStart := payloadStart)
    hperm
    rd2434
  exact bytesStoreX_setEmptyReturnFromWrite
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart)
    hwrite

theorem bytesStoreX_setEmptyLongHeaderWriteReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (payloadStart := payloadStart) hreach
  have hvalidHeader :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, ⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := StringStoreLite.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < oldLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldLen ⟨0⟩ = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := ⟨0⟩) (by
      have hpos : 0 < oldLen.toNat := by omega
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide] using hpos)
  have hshortZero : UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩ = ⟨1⟩ := by
    decide
  have hloopEntry := bytesStoreX_setCurrentCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (oldLen := oldLen) (len := (⟨0⟩ : UInt256))
    (ret := ⟨2434⟩)
    (tail := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  let count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := count) (base := ⟨0⟩ + StringStoreLite.clearCurrentBaseWord)
    (dead₀ := (⟨0⟩ : UInt256)) (dead₁ := oldLen) (dead₂ := (⟨0⟩ : UInt256))
    (ret := (⟨2434⟩ : UInt256))
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 6))
    (rdata := ByteArray.empty) (fuel := count.toNat)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2434⟩ := hloop
  have hwrite := bytesStoreX_setEmptyWriteZeroFrom2434
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := clearDataWordsForwardFrom I.codeOwner σ
      (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩ count.toNat)
    (payloadStart := payloadStart)
    (mem := StringStoreLite.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 6))
    (rdata := ByteArray.empty)
    hperm
    (by simpa [count] using rd2434)
  have hwrite6 : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩ count.toNat)
        ⟨0⟩ ⟨0⟩) k C := by
    simpa [StringStoreLite.clearCurrentHashAw6] using hwrite
  simpa [count] using
    bytesStoreX_setEmptyReturnFromWriteLongMem
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (payloadStart := payloadStart)
      hwrite6

theorem bytesStoreX_setEmptyLongMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem6
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setEmptyShortMalformed {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderEmpty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem6
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [⟨0⟩, ⟨2434⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := currentLengthZeroReturnMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setEmptyLongMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_setEmptyLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag)
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hbad)

theorem bytesStoreX_setEmptyShortMalformedCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_setEmptyShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (payloadStart := payloadStart) hreach
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag)
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hbad)

theorem bytesStoreX_setShortNonemptyReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.setHelperPayloadAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd592⟩ := hreach
  have haw : StringStoreLite.setHelperPayloadAw len = ⟨7⟩ :=
    StringStoreLite.setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
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
    raw mload 0 len (StringStoreLite.setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_mload128_short_nonzero_payloadAw
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  have rd273 := evm_run rd263 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (StringStoreLite.setHelperPayloadAw len)
      (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (StringStoreLite.clearCurrentBaseMemFrom_setPaddedMem_mload64_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0
      (StringStoreLite.setShortReturnMemAfterClearBase I.calldata len payloadStart)
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
      (StringStoreLite.setShortReturnMemAfterClearBase_mload64
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
          StringStoreLite.setShortReturnMemAfterClearBase_read192
            I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

theorem bytesStoreX_setShortNonemptyWriteReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    let payloadWord : UInt256 :=
      StringStoreLite.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  have hwrite := bytesStoreX_setShortNonemptyWriteHeaderAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hnz hshort hsrc
  exact bytesStoreX_setShortNonemptyReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner τ ⟨0⟩
      (UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart))))
    hnz hshort hsrc hwrite

theorem bytesStoreX_setWriteLongNoTailReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hwrite := bytesStoreX_setWriteLongFrom2434NoTailAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
    (len := len)
    hperm hnz hlong hlenMax hsrc hnoTailMod rd2434
  exact bytesStoreX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
        StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
        (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
        (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (len.toNat / 32))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreX_setWriteLongTailReturnAfterClearBase
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
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
        (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hwrite := bytesStoreX_setWriteLongFrom2434TailAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
    (len := len) (wordTail := wordTail)
    hperm hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail rd2434
  exact bytesStoreX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
          (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord wordTail len))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreX_setWriteLongNoTailReturnFromSetPadded
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
      ByteArray.empty (cA, τ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  obtain ⟨k', C', rd592⟩ :=
    bytesStoreX_setWriteLongFrom2434NoTail
      (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
      (len := len) (aw := StringStoreLite.setHelperEntryAw len)
      (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (rdata := ByteArray.empty)
      hperm hlong hnoTailMod rd2434
      (by
        intro i hi s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [StringStoreLite.longDataWordsLoopAw, hcur] at hnext
        rw [hcur, hnext])
  have hawLoop :
      StringStoreLite.longDataWordsLoopAw
          (StringStoreLite.clearCurrentHashAw
            (StringStoreLite.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ (len.toNat / 32) =
        StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len) :=
    StringStoreLite.longDataWordsLoopAw_setHelper_eq
      (len := len) hlenMax (len.toNat / 32) (by omega)
  have hwrite : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨k', C', by simpa [hawLoop] using rd592⟩
  exact bytesStoreX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
        StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
        (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
        (StringStoreLite.clearCurrentBaseMemFrom
          (StringStoreLite.setPaddedMem I.calldata len payloadStart))
        (len.toNat / 32))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreX_setWriteLongTailReturnFromSetPadded
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len)
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
        (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd2434⟩ := hreach
  have hmloadTail :
      (if (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart)).size ∨
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            StringStoreLite.longDataWordsLoopAw
              (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
              ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart)).readWithPadding
          (⟨128⟩ + StringStoreLite.longDataWordsLoopStride ⟨32⟩
            (len.toNat / 32)).toNat 32))) =
        wordTail := by
    simpa [hwordTail] using
      StringStoreLite.longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax
  obtain ⟨k', C', rd592⟩ :=
    bytesStoreX_setWriteLongFrom2434Tail
      (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (τ := τ) (payloadStart := payloadStart)
      (len := len) (wordTail := wordTail)
      (awTail := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      (aw := StringStoreLite.setHelperEntryAw len)
      (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (rdata := ByteArray.empty)
      hperm hlong htailMod rd2434
      (by
        intro i hi s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i)
          (off := (⟨128⟩ : UInt256) + StringStoreLite.longDataWordsLoopStride ⟨32⟩ i)
          s haw hstk]
        have hcur := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax i (Nat.le_of_lt hi)
        have hnext := StringStoreLite.longDataWordsLoopAw_setHelper_eq
          (len := len) hlenMax (i + 1) (Nat.succ_le_of_lt hi)
        simp [StringStoreLite.longDataWordsLoopAw, hcur] at hnext
        rw [hcur, hnext])
      (by
        intro s haw hstk
        rw [StringStoreLite.set_mloadCostSpec
          (aw := StringStoreLite.longDataWordsLoopAw
            (StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len)) ⟨128⟩ ⟨32⟩
              (len.toNat / 32))
          (off := (⟨128⟩ : UInt256) +
            StringStoreLite.longDataWordsLoopStride ⟨32⟩ (len.toNat / 32))
          s haw hstk])
      hmloadTail
      (StringStoreLite.longDataWordsLoopAw_setHelper_tail_mload_eq
        (len := len) hlenMax htailMod)
  have hwrite : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨592⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨k', C', rd592⟩
  exact bytesStoreX_setLongReturnFromWriteAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σ := σinit) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (σ' := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner τ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
          (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord wordTail len))
      ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
    hnz hlong hlenMax hsrc hwrite

theorem bytesStoreX_setLongNoTailReturnsOldShortFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  exact bytesStoreX_setWriteLongNoTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hlong hlenMax hsrc hnoTailMod

theorem bytesStoreX_setLongTailReturnsOldShortFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  exact bytesStoreX_setWriteLongTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (wordTail := wordTail)
    hperm hbranch hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail

theorem bytesStoreX_setLongNoTailReturnsOldLongNoClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (hnoTailMod : len.toNat % 32 = 0) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreX_setLongOldLongNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreX_setWriteLongNoTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hlong hlenMax hsrc hnoTailMod

theorem bytesStoreX_setLongTailReturnsOldLongNoClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart oldLen wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨0⟩)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  have hbranch := bytesStoreX_setLongOldLongNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreX_setWriteLongTailReturnFromSetPadded
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (wordTail := wordTail)
    hperm hbranch hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail

theorem bytesStoreX_setShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    let payloadWord : UInt256 :=
      StringStoreLite.setHelperPayloadWord I.calldata len payloadStart
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          payloadWord)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  have hbranch := bytesStoreX_setShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hreach hnz hlenMax hsrc hflag hvalid
  have hwrite := bytesStoreX_setShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hbranch hnz hshort
  exact bytesStoreX_setShortNonemptyReturnFromWrite
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hnz hshort hsrc hwrite

theorem bytesStoreX_setDecodeShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
    let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart))
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  dsimp only
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  simpa [len, payloadStart, hlenEvm] using
    bytesStoreX_setShortNonemptyReturns
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

theorem bytesStoreX_setDecodeShortNonemptyReturnsCurrentHeader {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
    let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart))
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ storedWord)
      (UInt256.toByteArray len) := by
  exact bytesStoreX_setDecodeShortNonemptyReturns
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign
    hlenMax hpayloadList hpayloadWord hnz hshort
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord] using hflag)
    (by simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord] using hvalid)

theorem bytesStoreX_writeBytesHelperShortHeaderReachWriteBranch
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
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
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C := by
  let oldLen : UInt256 :=
    UInt256.land
      (UInt256.div
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩))
        ⟨2⟩)
      ⟨127⟩
  have hcleanup := bytesStoreX_writeBytesHelperShortHeaderReachCleanup
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata) hreach hlenMax hflag hvalid hov
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotLong : UInt256.gt oldLen ⟨31⟩ = ⟨0⟩ := by
    exact currentLength_notGt31_of_lt32 holdLt32
  exact bytesStoreX_writeBytesCleanupOldShort
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldLen) (len := len)
    (ret := ⟨2643⟩) (tail := slot :: payloadStart :: len :: ret :: tail)
    (mem := mem) (aw := aw) (rdata := rdata)
    (by simpa [oldLen] using hcleanup)
    holdNotLong (by native_decide)
    (by simp only [List.length_cons]; omega)

private theorem bytesStoreX_pushChunkShortHeaderReachWriteBranch_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hhelper := bytesStoreX_pushChunkReachWriteHelperFromBody_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hperm hreach
  exact bytesStoreX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_pushChunkShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [chunksDataBase + bytesStoreChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        chunksDataBase + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreChunksDataBaseLiteral] using
    bytesStoreX_pushChunkShortHeaderReachWriteBranch_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart) hperm hreach hlenMax hflag' hvalid'

theorem bytesStoreX_writeBytesNewEmptyReachPackedHeader {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlenZero : len = ⟨0⟩)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
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

private theorem bytesStoreX_pushChunkEmptyReachPackedHeader_literal {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hbranch := bytesStoreX_pushChunkShortHeaderReachWriteBranch_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  exact bytesStoreX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreX_pushChunkEmptyReachPackedHeader {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩,
        chunksDataBase + bytesStoreChunksLengthWord σ I, payloadStart, len, ⟨1617⟩,
        chunksDataBase + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreChunksDataBaseLiteral] using
    bytesStoreX_pushChunkEmptyReachPackedHeader_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag' hvalid' hlenZero

theorem bytesStoreX_writeBytesNewShortNonemptyWriteHeader {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
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
    ∃ k C, RD bytesStoreBytecode I g
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
      ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_writeBytesNewLongReachLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (hlong : ¬ len.toNat < 32)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      ((⟨0⟩ : UInt256) :: bytesLikeDataBase slot ::
        UInt256.land len (UInt256.lnot ⟨31⟩) :: UInt256.gt len ⟨31⟩ ::
        (⟨0⟩ : UInt256) :: slot :: payloadStart :: len :: ret :: tail)
      (wordAt0Mem slot mem) (StringStoreLite.clearCurrentHashAw aw) rdata
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
        raw mstore (Cₘ (StringStoreLite.clearCurrentBaseAw aw) - Cₘ aw)
          (wordAt0Mem slot mem)
          (StringStoreLite.clearCurrentBaseAw aw) (by native_decide)
          (fun s haw hstk => by
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
              StringStoreLite.clearCurrentBaseAw])
          (by rfl) (by rfl) (by evm_ov),
        push1 ⟨32⟩, dup2,
        raw keccak256
          (Cₘ (StringStoreLite.clearCurrentHashAw aw) -
            Cₘ (StringStoreLite.clearCurrentBaseAw aw))
          (bytesLikeDataBase slot)
          (StringStoreLite.clearCurrentHashAw aw) (by native_decide)
          (fun s haw hstk => by
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
              StringStoreLite.clearCurrentHashAw, StringStoreLite.clearCurrentBaseAw])
          hslotHash (by rfl) (by evm_ov),
        push1 ⟨31⟩, not, dup8, and, swap2])⟩

theorem bytesStoreX_writeBytesNewLongDataWordsLoopStep
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx cutoff) = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
        (((⟨32⟩ : UInt256) + idx) :: ((⟨1⟩ : UInt256) + slot) :: cutoff ::
          gtFlag :: ((⟨32⟩ : UInt256) + stride) :: baseSlot :: payloadStart :: len ::
          ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (bytesStoreCalldataLongDataWord I payloadStart stride 0)) k' C' := by
  obtain ⟨_, _, rd2707⟩ := hreach
  have rd2716 := evm_run rd2707 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2739⟩,
    jumpiNT hcontinue]
  have rd2721pre := evm_run rd2716 with [dup7, dup6, add, calldataload, dup3]
  obtain ⟨_, _, rd2722₀⟩ := rd2721pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2722⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2722⟩
        (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
          ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (bytesStoreCalldataLongDataWord I payloadStart stride 0)) k C := by
    have hpc :
        ({ val := 2707 } + { val := 1 } + { val := 1 } + { val := 1 } +
              { val := 1 } + { val := 1 } + UInt256.ofNat 3 + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } : UInt256) = ⟨2722⟩ := by
      native_decide
    exact ⟨_, _, by
      simpa [hpc, bytesStoreCalldataLongDataWord,
        StringStoreLite.longDataWordsLoopStride, u256_add_comm payloadStart stride,
        sstoreAccountMap, initState] using rd2722₀⟩
  exact ⟨_, _, by
    simpa [u256_add_comm idx ⟨32⟩, u256_add_comm slot ⟨1⟩,
      u256_add_comm stride ⟨32⟩, List.append_assoc] using
      (evm_run rd2722 with [
        push1 ⟨32⟩, swap5, dup6, add, swap5, push1 ⟨1⟩, swap1,
        swap3, add, swap2, add, push2 ⟨2707⟩, jump (by native_decide)])⟩

theorem bytesStoreX_writeBytesNewLongDataWordsLoopGenerated
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
        (StringStoreLite.longDataWordsLoopIndex idx fuel ::
          StringStoreLite.longDataWordsLoopSlot slot fuel :: cutoff :: gtFlag ::
          StringStoreLite.longDataWordsLoopStride stride fuel :: baseSlot ::
          payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA,
          bytesStoreCalldataLongDataForwardFrom I.codeOwner τ slot payloadStart stride I fuel)
        k' C' := by
  induction fuel generalizing idx slot stride τ with
  | zero =>
      simpa [StringStoreLite.longDataWordsLoopIndex,
        StringStoreLite.longDataWordsLoopSlot,
        StringStoreLite.longDataWordsLoopStride,
        bytesStoreCalldataLongDataForwardFrom] using hreach
  | succ n ih =>
      have hstep := bytesStoreX_writeBytesNewLongDataWordsLoopStep
        (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (τ := τ) (idx := idx) (slot := slot)
        (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride)
        (baseSlot := baseSlot) (payloadStart := payloadStart) (len := len)
        (ret := ret) (tail := tail) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by
          simpa [StringStoreLite.longDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt
              (StringStoreLite.longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i)
              cutoff) =
              ⟨0⟩ := by
        intro i hi
        simpa [StringStoreLite.longDataWordsLoopIndex,
          StringStoreLite.longDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have htail := ih
        (idx := (⟨32⟩ : UInt256) + idx)
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        (τ := sstoreAccountMap I.codeOwner τ slot
          (bytesStoreCalldataLongDataWord I payloadStart stride 0))
        hstep hcontinueTail
      simpa [bytesStoreCalldataLongDataForwardFrom,
        StringStoreLite.longDataWordsLoopIndex,
        StringStoreLite.longDataWordsLoopSlot,
        StringStoreLite.longDataWordsLoopStride,
        StringStoreLite.longDataWordsLoopIndex_succ_base,
        StringStoreLite.longDataWordsLoopSlot_succ_base,
        StringStoreLite.longDataWordsLoopStride_succ_base,
        bytesStoreCalldataLongDataWord_succ_base] using htail

theorem bytesStoreX_writeBytesNewLongDataWordsLoopDoneNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
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
      ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_writeBytesNewLongNoTailFromWriteBranch
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, τ) k C)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret tail
        (wordAt0Mem slot mem) (StringStoreLite.clearCurrentHashAw aw) rdata
        (cA, sstoreAccountMap I.codeOwner
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner τ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopEntry := bytesStoreX_writeBytesNewLongReachLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata)
    hreach hlong (by omega)
  have hloop := bytesStoreX_writeBytesNewLongDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := bytesLikeDataBase slot)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨0⟩ : UInt256)) (baseSlot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := StringStoreLite.clearCurrentHashAw aw) (rdata := rdata)
    (fuel := len.toNat / 32)
    hperm hloopEntry
    (fun i hi => StringStoreLite.longDataLoopContinue len hi)
    hov
  exact bytesStoreX_writeBytesNewLongDataWordsLoopDoneNoTail
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := bytesStoreCalldataLongDataForwardFrom I.codeOwner τ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
    (idx := StringStoreLite.longDataWordsLoopIndex (⟨0⟩ : UInt256) (len.toNat / 32))
    (slot := StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := StringStoreLite.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
    (baseSlot := slot) (payloadStart := payloadStart) (len := len) (ret := ret)
    (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := StringStoreLite.clearCurrentHashAw aw) (rdata := rdata)
    hperm hloop
    (StringStoreLite.longDataLoopDone len)
    (StringStoreLite.longDataNoTail len hnoTailMod)
    hret hov

private theorem bytesStoreX_pushChunkShortNonemptyWriteHeaderFromBody_literal {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
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
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩,
        (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
          UInt256) + bytesStoreChunksLengthWord σ I)
        storedWord) k C := by
  dsimp only
  have hbranch := bytesStoreX_pushChunkShortHeaderReachWriteBranch_literal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  exact bytesStoreX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := (⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1617⟩)
    (tail := [(⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
        UInt256) + bytesStoreChunksLengthWord σ I, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)

private theorem bytesStoreX_pushChunkShortNonemptyWriteHeaderFromBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
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
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, chunksDataBase + bytesStoreChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩, chunksDataBase + bytesStoreChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I)
        storedWord) k C := by
  have hflag' :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                  UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hflag
  have hvalid' :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                      UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      ((⟨80084422859880547211683076133703299733277748156566366325829078699459944778998⟩ :
                          UInt256) + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreChunksDataBaseLiteral] using hvalid
  simpa [bytesStoreChunksDataBaseLiteral] using
    bytesStoreX_pushChunkShortNonemptyWriteHeaderFromBody_literal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag' hvalid' hnz hshort

theorem bytesStoreX_pushChunkEmptyWriteHeader {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot payloadStart len sel : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
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

theorem bytesStoreX_pushChunkEmptyWriteHeaderFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, chunksDataBase + bytesStoreChunksLengthWord σ I,
        payloadStart, len, ⟨1617⟩, chunksDataBase + bytesStoreChunksLengthWord σ I,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩) k C := by
  have hpacked := bytesStoreX_pushChunkEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hlenZero
  exact bytesStoreX_pushChunkEmptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreSelWord I)
    hperm hpacked hlenZero

theorem bytesStoreX_pushChunkReturnFromEmptyWrite {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len sel : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1623⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
          len, payloadStart, ⟨263⟩, sel]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1623₀⟩
  exact ⟨_, _, evm_run rd1623 with [
    swap3, swap2, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreX_pushChunkEmptyReachReturnWord {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [((sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreChunksLengthWord σ I + ⟨1⟩))
          (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩).find? I.codeOwner |>.option
            ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩) k C := by
  have hwrite := bytesStoreX_pushChunkEmptyWriteHeaderFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hlenZero
  exact bytesStoreX_pushChunkReturnFromEmptyWrite
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩))
      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreSelWord I) hwrite

theorem bytesStoreX_pushChunkShortNonemptyReachReturnWord {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
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
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I) storedWord
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ') k C := by
  dsimp only
  have hwrite := bytesStoreX_pushChunkShortNonemptyWriteHeaderFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hnz hshort
  exact bytesStoreX_pushChunkReturnFromEmptyWrite
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩))
      (chunksDataBase + bytesStoreChunksLengthWord σ I)
      (UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := chunksDataBase + bytesStoreChunksLengthWord σ I)
    (payloadStart := payloadStart) (len := len) (sel := bytesStoreSelWord I)
    hwrite

theorem bytesStoreX_pushChunkShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
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
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I) storedWord
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  exact bytesStoreX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (bytesStoreX_pushChunkShortNonemptyReachReturnWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag hvalid hnz hshort)

theorem bytesStoreX_pushChunkEmptyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreChunksLengthWord σ I + ⟨1⟩))
        (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨0⟩
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  exact bytesStoreX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (bytesStoreX_pushChunkEmptyReachReturnWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (len := len) (payloadStart := payloadStart)
      hperm hreach hlenMax hflag hvalid hlenZero)

theorem bytesStoreMappedLengthSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
      bytesStoreMappedLengthSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem_size]
  unfold bytesStoreMappedLengthSlot mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreMappedLengthKeyWord I) ⟨4⟩

theorem bytesStoreChunkLengthSlotHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase]
    using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreX_mappedLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreMappedLengthHeaderWord σ I, ⟨1137⟩,
        bytesStoreMappedLengthSlot I, ⟨0⟩, bytesStoreMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1113⟩ := hreach
  have hslot := bytesStoreMappedLengthSlotHash I
  have rd1127 := evm_run rd1113 with [
    jumpdest, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreMappedLengthKeyWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (bytesStoreMappedLengthSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1128₀⟩ := rd1127.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1128⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1129⟩
        [bytesStoreMappedLengthHeaderWord σ I, bytesStoreMappedLengthSlot I, ⟨0⟩,
          bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreMappedLengthHeaderWord, initState] using rd1128₀⟩
  exact ⟨_, _, evm_run rd1128 with [
    push2 ⟨1137⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_chunkLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreChunkLengthHeaderWord σ I, ⟨1137⟩,
        bytesStoreChunkLengthSlot I, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1693⟩ := hreach
  have hslot := bytesStoreChunkLengthSlotHash
  have rd1699 := evm_run rd1693 with [
    jumpdest, push0, push1 ⟨1⟩, dup3, dup2]
  obtain ⟨_, _, rd1700₀⟩ := rd1699.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1700⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreChunkLengthIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1700₀⟩
  have hlt : UInt256.lt (bytesStoreChunkLengthIndexWord I)
      (bytesStoreChunksLengthWord σ I) = ⟨1⟩ :=
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
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
        [bytesStoreChunkLengthHeaderWord σ I, bytesStoreChunkLengthSlot I, ⟨0⟩,
          bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunkLengthHeaderWord, bytesStoreChunkLengthSlot, initState]
        using rd1723₀⟩
  exact ⟨_, _, evm_run rd1723 with [
    push2 ⟨1137⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_chunkLengthOob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1693⟩ := hreach
  have rd1699 := evm_run rd1693 with [
    jumpdest, push0, push1 ⟨1⟩, dup3, dup2]
  obtain ⟨_, _, rd1700₀⟩ := rd1699.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1700⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreChunkLengthIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
          bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1700₀⟩
  have hlt : UInt256.lt (bytesStoreChunkLengthIndexWord I)
      (bytesStoreChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1700 with [
    dup2, lt, push2 ⟨1713⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1713⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_chunkLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩,
        bytesStoreChunkLengthSlot I, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderLongValidMem
    (bytesStoreX_chunkLengthReachDecoder hreach hbound) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_chunkLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        bytesStoreChunkLengthSlot I, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderShortValidMem
    (bytesStoreX_chunkLengthReachDecoder hreach hbound) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_chunkLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [len, bytesStoreChunkLengthSlot I, ⟨0⟩, bytesStoreChunkLengthIndexWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1137⟩ := hdecoded
  have rd263 := evm_run rd1137 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact bytesStoreX_returnWord263OfMem
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    ⟨_, _, rd263⟩

theorem bytesStoreX_chunkLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreX_chunkLengthReturnFromDecoded
    (bytesStoreX_chunkLengthDecoderLongValid hreach hbound hflag hvalid)

theorem bytesStoreX_chunkLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreX_chunkLengthReturnFromDecoded
    (bytesStoreX_chunkLengthDecoderShortValid hreach hbound hflag hvalid)

theorem bytesStoreX_chunkLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    (bytesStoreX_chunkLengthReachDecoder hreach hbound) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_chunkLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1693⟩
      [bytesStoreChunkLengthIndexWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    (bytesStoreX_chunkLengthReachDecoder hreach hbound) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_mappedLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩,
        bytesStoreMappedLengthSlot I, ⟨0⟩, bytesStoreMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderLongValidMem
    (bytesStoreX_mappedLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_mappedLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        bytesStoreMappedLengthSlot I, ⟨0⟩, bytesStoreMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreX_bytesLengthDecoderShortValidMem
    (bytesStoreX_mappedLengthReachDecoder hreach) hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_mappedLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1137⟩
      [len, bytesStoreMappedLengthSlot I, ⟨0⟩, bytesStoreMappedLengthKeyWord I, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd1137⟩ := hdecoded
  have rd263 := evm_run rd1137 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact bytesStoreX_returnWord263OfMem
    (mem := twoWordHashMem (bytesStoreMappedLengthKeyWord I) ⟨4⟩ solcFreePtrMem)
    (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size])
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
    ⟨_, _, rd263⟩

theorem bytesStoreX_mappedLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreX_mappedLengthReturnFromDecoded
    (bytesStoreX_mappedLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreX_mappedLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreX_mappedLengthReturnFromDecoded
    (bytesStoreX_mappedLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreX_mappedLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    (bytesStoreX_mappedLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_mappedLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1113⟩
      [bytesStoreMappedLengthKeyWord I, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    (bytesStoreX_mappedLengthReachDecoder hreach) hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreSetSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreSetByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x1c, 0x52, 0x47, 0x7d]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreSetPacketByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x0a, 0xb2, 0x59, 0x00]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStorePacketTagSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x99, 0x3e, 0x0a, 0x90]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreCurrentLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreClearCurrentSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStorePushChunkSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStorePacketLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreMappedLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x39, 0x1d, 0x72, 0x80]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreChunkLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreDecode_packetTag {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (packetTagGetter.params.map Param.name)
      (transitionSignature packetTagGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreDecode_currentLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (currentLengthGetter.params.map Param.name)
      (transitionSignature currentLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreDecode_clearCurrent {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (clearCurrentTransition.params.map Param.name)
      (transitionSignature clearCurrentTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreDecode_setByte {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata =
        some (bytesStoreSetByteLocals I) := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = _
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreSetByteIndexWord,
    bytesStoreSetByteValueWord, bytesStoreSetByteLocals]
    using decodeCalldata_uint256_uint8_ok (cd := I.calldata) (x := "index") (y := "value")
      hsz68 hhi hcanon

theorem bytesStoreDecode_setByte_none_noncanon_value {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreSetByteValueWord]
    using decodeCalldata_uint256_uint8_none_noncanon1 (cd := I.calldata) (x := "index")
      (y := "value") hsz68 hhi hnc

theorem bytesStoreDecode_setByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_short (cd := I.calldata) (x := "index")
      (y := "value") hshort

theorem bytesStoreDecode_setByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setByteTransition.params.map Param.name)
      (transitionSignature setByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_huge (cd := I.calldata) (x := "index")
      (y := "value") hbig

theorem bytesStoreDecode_setPacketByte {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata =
        some (((∅ : Store).insert "byteIndex"
          (.int (Int.ofNat (bytesStoreSetByteIndexWord I).toNat))).insert "value"
          (.int (Int.ofNat (bytesStoreSetByteValueWord I).toNat))) := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = _
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreSetByteIndexWord,
    bytesStoreSetByteValueWord]
    using decodeCalldata_uint256_uint8_ok (cd := I.calldata) (x := "byteIndex") (y := "value")
      hsz68 hhi hcanon

theorem bytesStoreDecode_setPacketByte_none_noncanon_value {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetByteValueWord I).toNat < EVM.twoPow 8) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8, bytesStoreSetByteValueWord]
    using decodeCalldata_uint256_uint8_none_noncanon1 (cd := I.calldata) (x := "byteIndex")
      (y := "value") hsz68 hhi hnc

theorem bytesStoreDecode_setPacketByte_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_short (cd := I.calldata) (x := "byteIndex")
      (y := "value") hshort

theorem bytesStoreDecode_setPacketByte_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setPacketByteTransition.params.map Param.name)
      (transitionSignature setPacketByteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["byteIndex", "value"] [uint256, uint8] I.calldata = none
  simpa [uint256, uint8, uint8Int, abiUInt256, abiUInt8]
    using decodeCalldata_uint256_uint8_none_huge (cd := I.calldata) (x := "byteIndex")
      (y := "value") hbig

theorem bytesStoreDecode_packetLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (packetLengthGetter.params.map Param.name)
      (transitionSignature packetLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreDecode_mappedLength {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata =
        some ((∅ : Store).insert "key"
          (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))) := by
  show decodeCalldata ["key"] [uint256] I.calldata = _
  simpa [uint256, abiUInt256, bytesStoreMappedLengthKeyWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "key") hsz36 hhi

theorem bytesStoreDecode_mappedLength_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["key"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "key") hshort

theorem bytesStoreDecode_mappedLength_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (mappedLengthGetter.params.map Param.name)
      (transitionSignature mappedLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["key"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "key") hbig

theorem bytesStoreDecode_chunkLength {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata =
        some (bytesStoreChunkLengthLocals I) := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = _
  simpa [uint256, abiUInt256, bytesStoreChunkLengthIndexWord,
    bytesStoreChunkLengthLocals]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "chunkIndex") hsz36 hhi

theorem bytesStoreDecode_chunkLength_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "chunkIndex") hshort

theorem bytesStoreDecode_chunkLength_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (chunkLengthGetter.params.map Param.name)
      (transitionSignature chunkLengthGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "chunkIndex") hbig

theorem bytesStoreDecode_pushChunk_none_short {I : ExecutionEnv}
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

theorem bytesStoreDecode_pushChunk_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_huge (x := "value") hbig

theorem bytesStoreDecode_pushChunk_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_offset_huge (x := "value") hsz36 hoff

theorem bytesStoreDecode_pushChunk_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (pushChunkTransition.params.map Param.name)
      (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_short (x := "value") hsz36 hhi hshort

theorem bytesStoreDecode_pushChunk_none_lengthHuge {I : ExecutionEnv}
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

theorem bytesStoreDecode_pushChunk_none_payloadShort {I : ExecutionEnv}
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

theorem bytesStoreDecode_pushChunk {I : ExecutionEnv}
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
      some ((∅ : Store).insert "value" (.bytes (StringStoreLite.setDecodedValueBytes I))) := by
  show decodeCalldata ["value"] [.bytes] I.calldata =
      some ((∅ : Store).insert "value" (.bytes (StringStoreLite.setDecodedValueBytes I)))
  simpa [StringStoreLite.setDecodedValueBytes] using
    decodeCalldata_bytes_some (cd := I.calldata) (x := "value")
      hsz36 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreDecode_pushChunk_empty {I : ExecutionEnv}
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

theorem bytesStoreChunkLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreachSel := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreChunkLengthLocals I) := by
    exact bytesStoreDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreChunkLengthIndexWord I).toNat <
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
        I.codeOwner (bytesStoreChunkLengthSlot I) =
          bytesStoreChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthRef I) =
          .ok (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreChunkLengthSlot I)
      (header := bytesStoreChunkLengthHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthLocals I) chunkLengthGetter.body
        (.returned
          { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreChunkLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreX_chunkLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hbound hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreChunkLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreachSel := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreChunkLengthLocals I) := by
    exact bytesStoreDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreChunkLengthIndexWord I).toNat <
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
        I.codeOwner (bytesStoreChunkLengthSlot I) =
          bytesStoreChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalidSolm :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreChunkLengthSlot I)
      (header := bytesStoreChunkLengthHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStoreChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthLocals I) chunkLengthGetter.body
        (.returned
          { contract := bytesStoreContract, locals := bytesStoreChunkLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.land
              (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreChunkLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreX_chunkLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hbound hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreChunkLengthOobRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreachSel := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreChunkLengthLocals I) := by
    exact bytesStoreDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      ¬ (bytesStoreChunkLengthIndexWord I).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner)
          ⟨1⟩).toNat := by
    rw [show
      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner) =
        I.codeOwner from rfl, hloadChunks]
    exact hbound
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreChunkLengthBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm
  exact (bytesStoreX_chunkLengthOob
      (g := Sat256.ofUInt256 g) hreach hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreChunkLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreachSel := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreChunkLengthLocals I) := by
    exact bytesStoreDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreChunkLengthIndexWord I).toNat <
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
        I.codeOwner (bytesStoreChunkLengthSlot I) =
          bytesStoreChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreChunkLengthSlot I)
      (header := bytesStoreChunkLengthHeaderWord σ_evm I)
      (bytesStoreChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreChunkLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreX_chunkLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hbound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreChunkLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreachSel := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_chunkLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (chunkLengthGetter.params.map Param.name)
        (transitionSignature chunkLengthGetter).paramTypes I.calldata =
          some (bytesStoreChunkLengthLocals I) := by
    exact bytesStoreDecode_chunkLength (I := I) hsz36 hhi
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hboundSolm :
      (bytesStoreChunkLengthIndexWord I).toNat <
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
        I.codeOwner (bytesStoreChunkLengthSlot I) =
          bytesStoreChunkLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunkLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreChunkLengthIndexWord I).toNat : Int)) =
          some (bytesStoreChunkLengthSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreChunkLengthSlot,
      u256_ofNat_toNat]
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbadSolm :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreChunkLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreChunkLengthSlot I)
      (header := bytesStoreChunkLengthHeaderWord σ_evm I)
      (bytesStoreChunkLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbadSolm])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreChunkLengthLocals I) chunkLengthGetter.body .reverted := by
    exact bytesStoreChunkLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hboundSolm hlen
  exact (bytesStoreX_chunkLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hbound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreChunkLengthRuntimeDecoded {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreChunkLengthIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat
  · by_cases hflag : UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid : UInt256.sub
          (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreChunkLengthShortValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hvalid
      · have hbad : UInt256.sub
            (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
          not_ne_iff.mp hvalid
        exact bytesStoreChunkLengthShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hbad
    · by_cases hvalid : UInt256.sub
          (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreChunkLengthLongValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hvalid
      · have hbad : UInt256.sub
            (UInt256.land (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (bytesStoreChunkLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
          not_ne_iff.mp hvalid
        exact bytesStoreChunkLengthLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound hflag hbad
  · exact bytesStoreChunkLengthOobRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hbound

theorem bytesStoreChunkLengthDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreach := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_chunkLength_none_short (I := I) hshort
  exact (bytesStoreX_chunkLengthDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreChunkLengthDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreChunkLengthSelector_size hsel
  have hreach := bytesStoreReachChunkLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_chunkLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_chunkLength_none_huge (I := I) hbig
  exact (bytesStoreX_chunkLengthDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreChunkLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 36
  · exact bytesStoreChunkLengthDecodeShortRuntime hcode hsize hperm hwv hsel hshort
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact bytesStoreChunkLengthRuntimeDecoded
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact bytesStoreChunkLengthDecodeHugeRuntime hcode hsize hperm hwv hsel hbig

theorem bytesStoreMappedLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreachSel := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreMappedLengthLocals I) := by
    simpa [bytesStoreMappedLengthLocals] using bytesStoreDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadMappedLength_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreMappedLengthSlot] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthRef I) =
          .ok (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreMappedLengthSlot I)
      (header := bytesStoreMappedLengthHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthLocals I) mappedLengthGetter.body
        (.returned
          { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreMappedLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_mappedLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreMappedLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreachSel := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreMappedLengthLocals I) := by
    simpa [bytesStoreMappedLengthLocals] using bytesStoreDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadMappedLength_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreMappedLengthSlot] using hload
  have hloadMapped' :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa using hloadMapped
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreMappedLengthSlot I)
      (header := bytesStoreMappedLengthHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStoreMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthLocals I) mappedLengthGetter.body
        (.returned
          { contract := bytesStoreContract, locals := bytesStoreMappedLengthLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat
              (UInt256.land
                (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreMappedLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_mappedLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land
            (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreMappedLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreachSel := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreMappedLengthLocals I) := by
    simpa [bytesStoreMappedLengthLocals] using bytesStoreDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreMappedLengthSlot] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreMappedLengthSlot I)
      (header := bytesStoreMappedLengthHeaderWord σ_evm I)
      (bytesStoreMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthLocals I) mappedLengthGetter.body .reverted := by
    exact bytesStoreMappedLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_mappedLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreMappedLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreachSel := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreach := bytesStoreX_mappedLengthDecodeValid
    (g := Sat256.ofUInt256 g) hreachSel hsz36 hhi hsize
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (mappedLengthGetter.params.map Param.name)
        (transitionSignature mappedLengthGetter).paramTypes I.calldata =
          some (bytesStoreMappedLengthLocals I) := by
    simpa [bytesStoreMappedLengthLocals] using bytesStoreDecode_mappedLength
      (I := I) hsz36 hhi
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreMappedLengthSlot I) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadMappedLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadMapped :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner
          (mappedValueSlot
            (.int ((bytesStoreMappedLengthKeyWord I).toNat : Int))) =
          bytesStoreMappedLengthHeaderWord σ_evm I := by
    simpa [bytesStoreMappedLengthSlot] using hload
  have hcodeOwner :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        I.codeOwner := by
    rfl
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreMappedLengthRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreMappedLengthSlot I)
      (header := bytesStoreMappedLengthHeaderWord σ_evm I)
      (bytesStoreMappedLengthRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hload)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreMappedLengthLocals I) mappedLengthGetter.body .reverted := by
    exact bytesStoreMappedLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_mappedLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreMappedLengthRuntimeDecoded {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreMappedLengthShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreMappedLengthShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hbad
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreMappedLengthLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreMappedLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreMappedLengthLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hflag hbad

theorem bytesStoreMappedLengthDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreach := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_mappedLength_none_short (I := I) hshort
  exact (bytesStoreX_mappedLengthDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreMappedLengthDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreMappedLengthSelector_size hsel
  have hreach := bytesStoreReachMappedLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_mappedLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_mappedLength_none_huge (I := I) hbig
  exact (bytesStoreX_mappedLengthDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_short (I := I) hshort
  exact (bytesStoreX_pushChunkDecodeShort
      (g := Sat256.ofUInt256 g) hreach hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_huge (I := I) hbig
  exact (bytesStoreX_pushChunkDecodeHuge
      (g := Sat256.ofUInt256 g) hreach hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_offsetHuge (I := I) hsz36 hoff
  exact (bytesStoreX_pushChunkDecodeOffsetHuge
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_lengthShort (I := I) hsz36 hhi hlenShort
  exact (bytesStoreX_pushChunkDecodeLengthShort
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax hlenShort)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_lengthHuge (I := I)
    hsz36 hhi hoffMax hlenWord hlenHuge
  exact (bytesStoreX_pushChunkDecodeLengthHuge
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax
      (StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (StringStoreLite.setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk_none_payloadShort (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreX_pushChunkDecodePayloadShort
      (g := Sat256.ofUInt256 g) hreach hsz36 hhi hsize hoffMax
      (StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
      hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStorePushChunkEmptyRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
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
          (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
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
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := bytesStoreDecode_pushChunk_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_zero I.calldata hlenZero
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
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreX_pushChunkEmptyReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
        (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        hperm hdecodedReach hlenMaxWord
        (bytesStorePushChunkEmptyFlagOfZero_of_ne (σ := σ_evm) (I := I)
          (by simpa [oldLen] using hne) (by simpa [oldLen] using hzero))
        (bytesStorePushChunkEmptyValidOfZero_of_ne (σ := σ_evm) (I := I)
          (by simpa [oldLen] using hne) (by simpa [oldLen] using hzero))
        hlenZero
  have hlenEq :
      bytesStoreChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + oldLen) =
        bytesStorePushChunkHeaderWord σ_evm I := by
      simpa [evmSolm0, oldLen, bytesStorePushChunkSlot] using
        bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts
    exact hload.trans (by
      simpa [oldLen, bytesStorePushChunkHeaderWord, bytesStorePushChunkSlot] using hzero)
  have hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evmSolm0 chunksRef (some (.bytes ByteArray.empty)) = .ok evmSolm1 := by
    simpa [evmSolm1] using
      bytesStorePushChunkEmptyPushArray_of_ne (evm := evmSolm0) oldLen
        (by simpa [oldLen] using hne) hloadLen hloadElem
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStorePushChunkEmptyBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
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
    simpa [bytesStoreChunksLengthWord] using
      bytesStoreChunksLengthWord_eq_storageLoad_of_accountMapEquiv
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

theorem bytesStorePushChunkEmptyShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
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
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := bytesStoreDecode_pushChunk_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_zero I.calldata hlenZero
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
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using congrArg (fun w => UInt256.land w ⟨1⟩) hheaderAfter |>.trans hflag
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreX_pushChunkEmptyReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
        (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        hperm hdecodedReach hlenMaxWord hflagAfter hvalidAfter hlenZero
  have hlenEq :
      bytesStoreChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evmSolm0 chunksRef (some (.bytes ByteArray.empty)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen] using
      bytesStorePushChunkEmptyPushArrayShortPacked_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStorePushChunkEmptyBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
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
    simpa [bytesStoreChunksLengthWord] using
      bytesStoreChunksLengthWord_eq_storageLoad_of_accountMapEquiv
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

theorem bytesStorePushChunkEmptyShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStorePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStorePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStorePushChunkHeaderWord,
      bytesStorePushChunkSlot] using
      bytesStorePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStorePushChunkSlot] using
      bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
      bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStorePushChunkEmptyShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStorePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hflag hvalid

set_option maxHeartbeats 4000000 in
theorem bytesStorePushChunkShortNonemptyShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.land (UInt256.div oldHeader ⟨2⟩) ⟨127⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let storedWord : UInt256 :=
    bytesStoreOptimizedShortStoredWord I len payloadStart
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
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
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
      bytesStoreOptimizedShortStoredWord I len payloadStart =
        solidityShortBytesWord (StringStoreLite.setDecodedValueBytes I) := by
    exact bytesStoreOptimizedShortStoredWord_abbrev_eq_solidityShortBytesWord
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
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap, storedWord, len, payloadStart, hlenEvm] using
      bytesStoreX_pushChunkShortNonemptyReturns
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
      bytesStoreChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [StringStoreLite.setDecodedValueBytes_size hpayloadList]
    exact hshort
  have hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen] using
      bytesStorePushChunkShortPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSize hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStorePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
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
    simpa [bytesStoreChunksLengthWord] using
      bytesStoreChunksLengthWord_eq_storageLoad_of_accountMapEquiv
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
theorem bytesStorePushChunkShortNonemptyShortPackedRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
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
    (hflag : UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStorePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStorePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStorePushChunkHeaderWord,
      bytesStorePushChunkSlot] using
      bytesStorePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStorePushChunkSlot] using
      bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
      bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStorePushChunkShortNonemptyShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStorePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hshort hflag hvalid

theorem bytesStorePushChunkLongMalformedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hbadAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hbad)
  have hrev := bytesStoreX_pushChunkLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    (len := uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
    (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    hperm hdecodedReach hlenMaxWord hflagAfter hbadAfter
  have hlenEq :
      bytesStoreChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .revert := by
    exact bytesStorePushChunkMalformedLongPushArray_of_post_header (evm := evmSolm0)
      oldLen oldHeader value hloadLen
      (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
      (by simpa [oldHeader] using hflag)
      (by simpa [oldHeader] using hbad)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
    exact bytesStorePushChunkBodyRevertsOfPush (evm := evmSolm0) (value := value)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStorePushChunkLongMalformedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
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
    (hflag : UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePushChunkHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStorePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStorePushChunkHeaderWord,
      bytesStorePushChunkSlot] using
      bytesStorePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStorePushChunkSlot] using
      bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
      bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStorePushChunkLongMalformedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStorePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hflag hbad

theorem bytesStorePushChunkShortMalformedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsz := bytesStorePushChunkSelector_size hsel
  have hreach := bytesStoreReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hbadAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hbad)
  have hrev := bytesStoreX_pushChunkShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    (len := uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
    (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    hperm hdecodedReach hlenMaxWord hflagAfter hbadAfter
  have hlenEq :
      bytesStoreChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .revert := by
    exact bytesStorePushChunkMalformedShortPushArray_of_post_header (evm := evmSolm0)
      oldLen oldHeader value hloadLen
      (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
      (by simpa [oldHeader] using hflag)
      (by simpa [oldHeader] using hbad)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body .reverted := by
    exact bytesStorePushChunkBodyRevertsOfPush (evm := evmSolm0) (value := value)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStorePushChunkShortMalformedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
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
    (hflag : UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStorePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePushChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStorePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStorePushChunkHeaderWord,
      bytesStorePushChunkSlot] using
      bytesStorePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStorePushChunkSlot] using
      bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) =
      bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStorePushChunkShortMalformedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStorePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hflag hbad

theorem bytesStoreDecode_set {I : ExecutionEnv}
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
      some ((∅ : Store).insert "value" (.bytes (StringStoreLite.setDecodedValueBytes I))) := by
  exact decodeCalldata_set_some
    (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList

theorem bytesStoreSetCurrentShortPostAccountMapEquiv {cA gh bl σ_evm σ_solm σ₀ A I}
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

theorem bytesStoreSetCurrentShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
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
    StringStoreLite.u256_div_add31_toNat_of_lt_sign (x := oldLen) holdLenLt
  have hcountNat :
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat =
        (oldLen.toNat + 31) / 32 := by
    rw [bytesStore_shiftRight_five_eq_div_thirtyTwo,
      StringStoreLite.uint256_sub_zero_right]
    exact hdivNat
  have hbase :
      (⟨0⟩ : UInt256) + StringStoreLite.clearCurrentBaseWord =
        solidityBytesDataBaseSlot ⟨0⟩ := by
    rw [u256_zero_add, StringStoreLite.clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
  simpa [initState, hcountNat, hbase, hstored] using
    accountMapEquiv_storageStore_clearSolidityBytesDataWordsFrom
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      hAccounts ⟨0⟩ 0 ((oldLen.toNat + 31) / 32) ⟨0⟩
      (solidityShortBytesWord value)

theorem bytesStoreSetCurrentShortCreatedAccounts {cA gh bl σ_solm σ₀ A I}
    {g : UInt256} {value : ByteArray} :
    cA =
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ (solidityShortBytesWord value)).createdAccounts := by
  simp only [storageStore_createdAccounts, initState]

theorem bytesStoreSetNewLongOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let dataFuel : Nat := (value.size + 31) / 32
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ value 0 dataFuel)
    (writeSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ value 0 dataFuel).executionEnv.codeOwner
    ⟨0⟩ header
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [StringStoreLite.setDecodedValueBytes_size hpayloadList]
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
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hvalid
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreWriteCurrentLongPacked (evm := evmSolm0)
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen)
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
        RDret bytesStoreBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
              StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
              (StringStoreLite.clearCurrentBaseMemFrom
                (StringStoreLite.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreX_setLongNoTailReturnsOldShortFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore hvalidCore hmod
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          accountMapEquiv_sstore_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := StringStoreLite.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len))
            (mem := StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32) (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hdataFuelEq : dataFuel = len.toNat / 32 := by
        dsimp [dataFuel]
        rw [hsizeDecoded]
        have hdiv := Nat.div_add_mod len.toNat 32
        omega
      have hdataBridge := StringStoreLite.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
        (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
        hnz hlenMaxLen hsrc hsizeDecoded (by rfl) (by rfl) hoffMax
        (τ := σ_solm) (i := 0) (fuel := len.toNat / 32) (by omega)
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : StringStoreLite.clearCurrentBaseWord + UInt256.ofNat 0 =
            StringStoreLite.clearCurrentBaseWord := by
          simpa using StringStoreLite.uint256_add_zero_right
            StringStoreLite.clearCurrentBaseWord
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [hdataFuelEq, hbase0, hstride] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
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
          (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    have hret :
        RDret bytesStoreBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                (len.toNat / 32))
              (StringStoreLite.longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreX_setLongTailReturnsOldShortFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (wordTail := wordTail)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore hvalidCore hmod
        (by rfl) (by rfl) hoffMax hwordTail
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                  StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                  (StringStoreLite.clearCurrentBaseMemFrom
                    (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                  (len.toNat / 32))
                (StringStoreLite.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          accountMapEquiv_sstore_tail_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := StringStoreLite.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len))
            (mem := StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32)
            (tailSlot := StringStoreLite.longDataWordsLoopSlot
              StringStoreLite.clearCurrentBaseWord (len.toNat / 32))
            (tailWord := StringStoreLite.longDataTailMaskedWord wordTail len)
            (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
        dsimp [dataFuel]
        rw [hsizeDecoded]
        have hdiv := Nat.div_add_mod len.toNat 32
        have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      have hdataBridge := StringStoreLite.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
        (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
        (owner := I.codeOwner)
        hnz hlenMaxLen hsrc hsizeDecoded hlong (by rfl) (by rfl) hoffMax hmod (by rfl) σ_solm
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                  StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                  (StringStoreLite.clearCurrentBaseMemFrom
                    (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                  (len.toNat / 32))
                (StringStoreLite.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : StringStoreLite.clearCurrentBaseWord + UInt256.ofNat 0 =
            StringStoreLite.clearCurrentBaseWord := by
          simpa using StringStoreLite.uint256_add_zero_right
            StringStoreLite.clearCurrentBaseWord
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [hdataFuelEq, hbase0, hstride] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap] using hret) hd hdec hwrite hCreated
      hAccountsPost henc

theorem bytesStoreSetNewShortOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart))
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩
    (solidityShortBytesWord value)
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord)
        (UInt256.toByteArray len) := by
    simpa [len, payloadStart, storedWord] using
      bytesStoreX_setDecodeShortNonemptyReturnsCurrentHeader
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreWriteCurrentDecodedShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts (by rfl) hpayloadList hnewShort hflag hvalid
    simpa [evmSolm0, evmSolm1, value, initState] using hwrite₀
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, len, payloadStart] using
      bytesStoreSetHelperShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        (by rfl) (by rfl) hoffMax hnz hnewShort hsrc hpayloadList
  have hCreated : cA = evmSolm1.createdAccounts := by
    simpa [evmSolm1, evmSolm0, value, initState] using
      bytesStoreSetCurrentShortCreatedAccounts
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (value := value)
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord)
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0, value, initState] using
      bytesStoreSetCurrentShortPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (storedWord := storedWord) (value := value) hAccounts hstored
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    have hlenSize : len.toNat = value.size := by
      dsimp [value, len]
      rw [StringStoreLite.setDecodedValueBytes_size hpayloadList]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [← hlenSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (o := UInt256.toByteArray len)
    (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ storedWord))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreSetNewShortOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldLen : UInt256 := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (StringStoreLite.setHelperPayloadWord I.calldata len payloadStart))
  let τ : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ (solidityShortBytesWord value)
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
        [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hvalid
  have holdLenCore :
      oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord]
  have hbranch := bytesStoreX_setShortLongHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
    (oldLen := oldLen)
    hperm hdecodedReachLen hnz hnewShort (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hsrc hflagCore holdLenCore hvalidCore
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
        (UInt256.toByteArray len) := by
    simpa [τ, storedWord] using
      bytesStoreX_setShortNonemptyWriteReturnAfterClearBase
        (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (τ := τ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart)
        hperm hbranch hnz hnewShort hsrc
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreWriteCurrentDecodedShortFromLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts (by rfl) hpayloadList hnewShort hflag hvalid
    simpa [evmSolm0, evmSolm1, value, oldLen, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, len, payloadStart] using
      bytesStoreSetHelperShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        (by rfl) (by rfl) hoffMax hnz hnewShort hsrc hpayloadList
  have holdLenLt : oldLen.toNat < 2 ^ 255 := by
    exact StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen) (by rfl)
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord)
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0, oldLen, value, τ, initState] using
      bytesStoreSetCurrentShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    have hlenSize : len.toNat = value.size := by
      dsimp [value, len]
      rw [StringStoreLite.setDecodedValueBytes_size hpayloadList]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [← hlenSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (o := UInt256.toByteArray len)
    (acc := (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ storedWord))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreSetEmptyShortValidRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hvalid
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
        (UInt256.toByteArray ⟨0⟩) :=
    bytesStoreX_setEmptyShortHeaderWriteReturn
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hperm hreach hflagCore hvalidCore
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreWriteCurrentEmptyShortPacked
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
  exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    (o := UInt256.toByteArray ⟨0⟩)
    (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩))
    (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreWriteCurrentEmptyLongOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlen : oldLen = UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
      I.codeOwner ⟨0⟩ ⟨0⟩
    writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
      .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ ⟨0⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite₀ := bytesStoreWriteCurrentShortFromLongPrepared
    (evm := evmSolm0) (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (len := oldLen) (value := ByteArray.empty)
    (by decide) hload hflag hlen hvalid
  simpa [evmSolm0, evmSolm1, initState, hshortEmpty,
    clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀

theorem bytesStoreSetCurrentEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
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
    bytesStoreSetCurrentShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

set_option maxHeartbeats 4000000 in
theorem bytesStoreSetEmptyLongValidRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let acc : Batteries.RBSet AccountAddress compare × AccountMap :=
    (cA, sstoreAccountMap I.codeOwner
      (clearDataWordsForwardFrom I.codeOwner σ_evm
        (⟨0⟩ + StringStoreLite.clearCurrentBaseWord) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
      ⟨0⟩ ⟨0⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    I.codeOwner ⟨0⟩ ⟨0⟩
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag
  have hvalidCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hvalid
  have holdLenCore :
      oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord]
  have hret : RDret bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray ⟨0⟩) := by
    simpa [acc] using
      bytesStoreX_setEmptyLongHeaderWriteReturn
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (payloadStart := payloadStart) (oldLen := oldLen)
        hperm hreach hflagCore holdLenCore hvalidCore
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreWriteCurrentEmptyLongOfAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (oldLen := oldLen)
        hAccounts (by rfl) hflag (by simpa [oldLen] using hvalid)
  have holdLenLt : oldLen.toNat < 2 ^ 255 := by
    exact StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen) (by rfl)
  have hCreated : acc.1 = evmSolm1.createdAccounts := by
    simp [acc, evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv acc.2 evmSolm1.accountMap := by
    simpa [acc, evmSolm1, evmSolm0] using
      bytesStoreSetCurrentEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (oldLen := oldLen)
        hAccounts holdLenLt
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int ByteArray.empty.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    (o := UInt256.toByteArray ⟨0⟩) (acc := acc) (evmCurrent := evmSolm1)
    hcode hwv hret hd hdec hwrite hCreated hAccountsPost henc

theorem bytesStoreSetEmptyLongMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev :
      RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreX_setEmptyLongMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hreach hflag hbad
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert := by
    have hwrite₀ := bytesStoreWriteCurrentMalformedLongOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    hcode hwv hrev hd hdec hwrite

theorem bytesStoreSetEmptyShortMalformedRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {payloadStart : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes ByteArray.empty)))
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev :
      RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    bytesStoreX_setEmptyShortMalformedCurrentHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
      hreach hflag hbad
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert := by
    have hwrite₀ := bytesStoreWriteCurrentMalformedShortOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
      hAccounts hflag hbad
    simpa [evmSolm0] using hwrite₀
  exact bytesStoreSetRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty)
    hcode hwv hrev hd hdec hwrite

theorem bytesStoreSetEmptyRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_zero I.calldata hlenZero
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
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hreach :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
        [⟨0⟩, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [payloadStart, hlenZero] using hdecodedReach
  by_cases hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetEmptyShortValidRuntimeOfReach
        hcode hperm hwv hAccounts hreach hd hdec hflag hvalid
    · exact bytesStoreSetEmptyShortMalformedRuntimeOfReach
        hcode hwv hAccounts hreach hd hdec hflag (not_ne_iff.mp hvalid)
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetEmptyLongValidRuntimeOfReach
        hcode hperm hwv hAccounts hreach hd hdec hflag hvalid
    · exact bytesStoreSetEmptyLongMalformedRuntimeOfReach
        hcode hwv hAccounts hreach hd hdec hflag (not_ne_iff.mp hvalid)

theorem bytesStoreSetDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetSelector_size hsel
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_headShort (I := I) hsz hshort
  exact (bytesStoreX_setDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetSelector_size hsel
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_huge (I := I) hbig
  exact (bytesStoreX_setDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_offsetHuge (I := I) hsz36 hoff
  exact (bytesStoreX_setDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_lengthShort
    (I := I) hsz36 hhi hlenShort
  exact (bytesStoreX_setDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax hlenShort)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_lengthHuge
    (I := I) hsz36 hhi hoffMax hlenWord hlenHuge
  exact (bytesStoreX_setDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax
      (StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (StringStoreLite.setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := decodeCalldata_set_none_payloadShort
    (I := I) hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreX_setDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax
      (StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
      hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetNewShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetNewShortOldShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
    · exact bytesStoreSetRawDecodedNonemptyShortMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetNewShortOldLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewShort hflag hvalid
    · exact bytesStoreSetRawDecodedNonemptyLongMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)

theorem bytesStoreSetDecodedShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩
  · exact bytesStoreSetEmptyRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenZero
  · have hlenAbi :
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) =
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
      simpa using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
    have hnz :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
      intro hz
      apply hlenZero
      apply u256_inj
      simpa [hlenAbi] using hz
    exact bytesStoreSetNewShortRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
      hlenMax hpayloadList hpayloadWord hnz hnewShort

theorem bytesStoreMappedLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 36
  · exact bytesStoreMappedLengthDecodeShortRuntime hcode hsize hperm hwv hsel hshort
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact bytesStoreMappedLengthRuntimeDecoded
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact bytesStoreMappedLengthDecodeHugeRuntime hcode hsize hperm hwv hsel hbig

theorem bytesStorePacketTagRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz := bytesStorePacketTagSelector_size hsel
  have hreach := bytesStoreReachPacketTag (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_packetTag (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_packetTag (I := I) hsz
  have hword : packetTagWord σ_evm I = packetTagWord σ_solm I :=
    packetTagWord_eq_of_accountMapEquiv hAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        packetTagGetter.body
        (.returned { contract := bytesStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (packetTagWord σ_solm I).toNat)))) := by
    simpa [packetTagWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      bytesStorePacketTagBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (bytesStoreX_packetTag (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (packetTagWord σ_evm I)))

theorem bytesStoreCurrentLengthLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreCurrentLengthSelector_size hsel
  have hreach := bytesStoreReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact bytesStoreCurrentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_currentLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreCurrentLengthShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreCurrentLengthSelector_size hsel
  have hreach := bytesStoreReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact bytesStoreCurrentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_currentLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreClearCurrentLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact bytesStoreClearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_clearCurrentLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreClearCurrentShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact bytesStoreClearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_clearCurrentShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreClearCurrentShortZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hheader : bytesStoreCurrentLengthHeaderWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    decide
  have hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hheader]
    decide
  have hzero : UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ =
      ⟨0⟩ := by
    rw [hheader]
    decide
  have hret := bytesStoreX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hvalid hzero
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hload' :
        Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
          bytesStoreCurrentLengthHeaderWord σ_evm I := by
      simpa [evmSolm0, initState] using
        bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts
    simpa [hheader] using hload'
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    simpa [evmSolm0, initState] using hload
  have hread :
      evalExpr? bytesStoreConfig { contract := bytesStoreContract, locals := ∅ }
        evmSolm0 (.storage currentRef) = .ok (.bytes ByteArray.empty) := by
    exact evalSolidityBytesEmptyOfZeroHeader
      (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
      (solm := { contract := bytesStoreContract, locals := ∅ })
      (evm := evmSolm0) (ref := currentRef) (er := { base := "current" })
      (baseSlot := ⟨0⟩)
      rfl (bytesStoreCurrentLengthResolve evmSolm0)
      bytesStoreCurrentLengthBaseSlot hloadBytes
  have hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreDeleteCurrentShortZero (evm := evmSolm0) hload
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
          evmSolm1 (some (.int 0))) := by
    exact bytesStoreClearCurrentBodyReturnsZero (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hread hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simpa [evmSolm1, evmSolm0] using
        accountMapEquiv_storageStore_initState_codeOwner
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreClearCurrentShortNonzeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hret := bytesStoreX_clearCurrentShortValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hlen hvalid hnonzero
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  obtain ⟨copy, hread, hcopySize⟩ :=
    bytesStoreReadCurrentShortPackedExists (evm := evmSolm0)
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len)
      hloadBytes hflag hlen hvalid
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreDeleteCurrentShortPacked (evm := evmSolm0)
        (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len) (copy := copy)
        hloadBytes hpacked hflag hlen hvalid
  have hbodyBytes := bytesStoreClearCurrentBodyReturnsBytes
    (evm := evmSolm0) (evm' := evmSolm1) (copy := copy)
    (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreContract,
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

theorem bytesStoreCurrentLengthLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreCurrentLengthSelector_size hsel
  have hreach := bytesStoreReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat :=
    bytesStoreReadCurrentLengthLong_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact bytesStoreCurrentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_currentLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreCurrentLengthShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreCurrentLengthSelector_size hsel
  have hreach := bytesStoreReachCurrentLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz _hsize hsel
  have hd := bytesStoreDispatch_currentLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_currentLength (I := I) hsz
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat :=
    bytesStoreReadCurrentLengthShort_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat
              (UInt256.land
                (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact bytesStoreCurrentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreX_currentLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreCurrentLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreCurrentLengthShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreCurrentLengthShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreCurrentLengthLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreCurrentLengthLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad

theorem bytesStorePacketLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz := bytesStorePacketLengthSelector_size hsel
  have hreach := bytesStoreReachPacketLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreDispatch_packetLength (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_packetLength (I := I) hsz
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ = bytesStorePacketLengthHeaderWord σ_evm I := by
    simpa [bytesStorePacketLengthHeaderWord, initState] using
      bytesStoreStorageLoad_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) ⟨2⟩ hAccounts
  by_cases hflag : UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · have hvalid0 :
          UInt256.sub ⟨0⟩
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
        simpa [hflag] using hvalid
      have hlen :
          readStorageBytesLength? bytesStoreConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } =
              .ok (UInt256.land
                (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
        exact bytesStoreReadLengthOfHeaderLoad
          (er := bytesStorePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStorePacketLengthHeaderWord σ_evm I)
          (len := (UInt256.land
            (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
          (bytesStorePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
      have hbody :
          ExecTransitionBody bytesStoreConfig bytesStoreContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body
            (.returned { contract := bytesStoreContract, locals := ∅ }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some (.int
                (Int.ofNat
                  (UInt256.land
                    (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
        exact bytesStorePacketLengthBodyReturnsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreX_packetLengthShortValid
          (g := Sat256.ofUInt256 g) hreach hflag hvalid)
        |>.reEquivExecution hcode hd hdec hbody hAccounts
          (returnEquiv_of_encode
            (uint256ReturnEncoding
              (UInt256.land
                (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))
    · have hbad : UInt256.sub
          (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      have hbad0 :
          UInt256.sub ⟨0⟩
            (UInt256.lt
              (UInt256.land (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
        simpa [hflag] using hbad
      have hlen :
          readStorageBytesLength? bytesStoreConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } = .revert := by
        exact bytesStoreReadLengthRevertOfHeaderLoad
          (er := bytesStorePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStorePacketLengthHeaderWord σ_evm I)
          (bytesStorePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
      have hbody :
          ExecTransitionBody bytesStoreConfig bytesStoreContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body .reverted := by
        exact bytesStorePacketLengthBodyRevertsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreX_packetLengthShortMalformed
          (g := Sat256.ofUInt256 g) hreach hflag hbad)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · have hlen :
          readStorageBytesLength? bytesStoreConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } =
              .ok (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
        exact bytesStoreReadLengthOfHeaderLoad
          (er := bytesStorePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStorePacketLengthHeaderWord σ_evm I)
          (len := (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
          (bytesStorePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
      have hbody :
          ExecTransitionBody bytesStoreConfig bytesStoreContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body
            (.returned { contract := bytesStoreContract, locals := ∅ }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some (.int
                (Int.ofNat (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
        exact bytesStorePacketLengthBodyReturnsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreX_packetLengthLongValid
          (g := Sat256.ofUInt256 g) hreach hflag hvalid)
        |>.reEquivExecution hcode hd hdec hbody hAccounts
          (returnEquiv_of_encode
            (uint256ReturnEncoding (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩)))
    · have hbad : UInt256.sub
          (UInt256.land (bytesStorePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStorePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      have hlen :
          readStorageBytesLength? bytesStoreConfig
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            { base := "packet", steps := [.field "data"] } = .revert := by
        exact bytesStoreReadLengthRevertOfHeaderLoad
          (er := bytesStorePacketDataRef)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (baseSlot := ⟨2⟩)
          (header := bytesStorePacketLengthHeaderWord σ_evm I)
          (bytesStorePacketDataRef_length_slot
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
          (by simpa [initState] using hload)
          (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
      have hbody :
          ExecTransitionBody bytesStoreConfig bytesStoreContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
            packetLengthGetter.body .reverted := by
        exact bytesStorePacketLengthBodyRevertsOfLength
          (by simp only [initState]; exact hwv) hlen
      exact (bytesStoreX_packetLengthLongMalformed
          (g := Sat256.ofUInt256 g) hreach hflag hbad)
        |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStore
