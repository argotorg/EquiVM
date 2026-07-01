import Examples.BytesStoreLite.CoreBytecode
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
# BytesStoreLiteCore — lightweight proof scaffold

The reduced example keeps only one Solidity `string` slot:

* `set(bytes)` exercises ABI dynamic string input and whole-value storage write;
* `clearCurrent()` exercises whole-value storage read plus clear;
* `currentLength()` exercises the string length read.

This module intentionally stops at cheap Solm-side and dispatch facts. Runtime equivalence proofs
can now be added one function at a time without making the default string smoke test carry the
old `bytes` duplicate path.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BytesStoreLiteCore

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-! ## Dispatch selectors -/

/-- Function selectors, in `bytesStoreLiteCoreContract.transitions` order. -/
def bytesStoreLiteCoreSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x03, 0x99, 0x32, 0x1e]⟩ -- set(bytes)
  | 1 => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ -- clearCurrent()
  | _ => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ -- currentLength()

/-- Selectors in the linear bytecode dispatcher arm order chosen by solc. -/
def bytesStoreLiteCoreArmSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x03, 0x99, 0x32, 0x1e]⟩ -- set(bytes)
  | 1 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ -- currentLength()
  | _ => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ -- clearCurrent()

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev bytesStoreLiteCoreSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The first selector arm after the standard solc dispatch prefix. -/
abbrev bytesStoreLiteCoreFirstArmPc : UInt256 := ⟨30⟩

theorem bytesStoreLiteCoreTransitions :
    bytesStoreLiteCoreContract.transitions =
      [setTransition, clearCurrentTransition, currentLengthGetter] :=
  rfl

/-- `ByteArray` `==` reflects equality. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

theorem bytesStoreLiteCoreArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed bytesStoreLiteCoreBytecode
      (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem bytesStoreLiteCoreArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 3) :
    UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc j))
        (bytesStoreLiteCoreSelWord I)
      = if (bytesStoreLiteCoreArmSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem bytesStoreLiteCoreArmMatches {I : ExecutionEnv} (i : Nat) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (bytesStoreLiteCoreArmSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc j))
        (bytesStoreLiteCoreSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc i))
        (bytesStoreLiteCoreSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = bytesStoreLiteCoreArmSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [bytesStoreLiteCoreArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [bytesStoreLiteCoreArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem bytesStoreLiteCoreReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : Nat) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc j))
        (bytesStoreLiteCoreSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc i))
        (bytesStoreLiteCoreSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J bytesStoreLiteCoreBytecode 0).contains bodyPC = true)
    (hbody : armTgt bytesStoreLiteCoreBytecode
        (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc i) = bodyPC) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc := by
    solc_dispatch_prefix
  simpa [bytesStoreLiteCoreSelWord, solcSelectorWord] using
    (solcDispatchReachBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := bytesStoreLiteCoreBytecode) (firstArmPc := bytesStoreLiteCoreFirstArmPc)
      (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest)
      (fun j hj => bytesStoreLiteCoreArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [bytesStoreLiteCoreSelWord, solcSelectorWord] using heq0 j hj)
      (by simpa [bytesStoreLiteCoreSelWord, solcSelectorWord] using htake)
      hjd hbody)

theorem bytesStoreLiteCoreReachCurrentLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨115⟩
        [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  rcases bytesStoreLiteCoreArmMatches 1 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteCoreArmSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact bytesStoreLiteCoreReachBody 1 (by decide) ⟨115⟩ hcode hwv hsz hsize heq0 htake
    (by jump_dest) (by decide)

theorem bytesStoreLiteCoreReachClearCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨145⟩
        [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  rcases bytesStoreLiteCoreArmMatches 2 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteCoreArmSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact bytesStoreLiteCoreReachBody 2 (by decide) ⟨145⟩ hcode hwv hsz hsize heq0 htake
    (by jump_dest) (by decide)

theorem bytesStoreLiteCoreReachSet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨67⟩
        [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  rcases bytesStoreLiteCoreArmMatches 0 (by decide) hsz
      (by simpa [selIs, bytesStoreLiteCoreArmSelBytes] using hsel) with
    ⟨heq0, htake⟩
  exact bytesStoreLiteCoreReachBody 0 (by decide) ⟨67⟩ hcode hwv hsz hsize heq0 htake
    (by jump_dest) (by decide)

theorem bytesStoreLiteCoreReachSetDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨645⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨88⟩, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreLiteCoreReachSet
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hsizeWord :
      (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size := by
    exact uadd_lit_usub_ofNat_lit hsz hsize
  exact ⟨_, _, by
    simpa [hsizeWord] using
      (evm_run hreach with [
        jumpdest, push2 ⟨93⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
        push2 ⟨88⟩, swap2, swap1, push2 ⟨645⟩,
        jump (by jump_dest) ])⟩

theorem bytesStoreLiteCoreDispatch_set {cd : ByteArray}
    (hsel : (⟨#[0x03, 0x99, 0x32, 0x1e]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteCoreContract cd = some setTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteCoreContract)
    (pre := [])
    (post := [clearCurrentTransition, currentLengthGetter])
    (ti := setTransition)
    (cd := cd) bytesStoreLiteCoreTransitions ?_ ?_
  · intro t ht
    simp at ht
  · rw [selectorOf, setBytesSelectorBytes]
    exact hsel

theorem bytesStoreLiteCoreDispatch_currentLength {cd : ByteArray}
    (hsel : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteCoreContract cd = some currentLengthGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteCoreContract)
    (pre := [setTransition, clearCurrentTransition])
    (post := [])
    (ti := currentLengthGetter)
    (cd := cd) bytesStoreLiteCoreTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht
    · subst t; rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]; decide
    · subst t; rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]; decide
  · rw [selectorOf, currentLengthSelectorBytes]
    exact hsel

theorem bytesStoreLiteCoreDispatch_clearCurrent {cd : ByteArray}
    (hsel : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteCoreContract cd = some clearCurrentTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteCoreContract)
    (pre := [setTransition])
    (post := [currentLengthGetter])
    (ti := clearCurrentTransition)
    (cd := cd) bytesStoreLiteCoreTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht
    · subst t; rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes]
    exact hsel

theorem bytesStoreLiteCoreDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg bytesStoreLiteCoreContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, bytesStoreLiteCoreTransitions]
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with ht | ht | ht
    · subst t; rw [selectorOf, setBytesSelectorBytes]; rfl
    · subst t; rw [selectorOf, clearCurrentSelectorBytes]; rfl
    · subst t; rw [selectorOf, currentLengthSelectorBytes]; rfl) h

theorem bytesStoreLiteCoreDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 3 → (bytesStoreLiteCoreSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg bytesStoreLiteCoreContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, bytesStoreLiteCoreTransitions]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp at ht
  rcases ht with ht | ht | ht
  · subst t
    rw [selectorOf, setBytesSelectorBytes]
    simpa [bytesStoreLiteCoreSelBytes] using hnm 0 (by omega)
  · subst t
    rw [selectorOf, clearCurrentSelectorBytes]
    simpa [bytesStoreLiteCoreSelBytes] using hnm 1 (by omega)
  · subst t
    rw [selectorOf, currentLengthSelectorBytes]
    simpa [bytesStoreLiteCoreSelBytes] using hnm 2 (by omega)

theorem bytesStoreLiteCoreDecode_currentLength {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (currentLengthGetter.params.map Param.name)
      (transitionSignature currentLengthGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem bytesStoreLiteCoreDecode_clearCurrent {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (clearCurrentTransition.params.map Param.name)
      (transitionSignature clearCurrentTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

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

def setDecodedValueBytes (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk
    ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).toArray)

theorem setDecodedValueBytes_toList {I : ExecutionEnv} :
    (setDecodedValueBytes I).toList =
      (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) := by
  simp [setDecodedValueBytes, byteArray_toList_eq]

theorem setDecodedValueBytes_size {I : ExecutionEnv}
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    (setDecodedValueBytes I).size =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
  let payload := (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
  change payload.toArray.size =
    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
  rw [show payload.toArray.size = payload.length by simp]
  simpa [payload] using hpayload

theorem setDecodedValueBytes_readWithPadding_short_toList {I : ExecutionEnv}
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnonzero :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    ((setDecodedValueBytes I).readWithPadding 0 32).toList =
      (setDecodedValueBytes I).toList ++
        List.replicate
          (32 - (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
          0 := by
  have hsz := setDecodedValueBytes_size (I := I) hpayload
  have hpos : (setDecodedValueBytes I).size ≠ 0 := by
    rw [hsz]
    exact hnonzero
  have hshort' : (setDecodedValueBytes I).size < 32 := by
    rw [hsz]
    exact hshort
  simpa [hsz] using
    readWithPadding_zero_toList_of_size_lt32 (setDecodedValueBytes I) hpos hshort'

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
      some ((∅ : Store).insert "value" (.bytes (setDecodedValueBytes I))) := by
  show decodeCalldata ["value"] [.bytes] I.calldata =
      some ((∅ : Store).insert "value" (.bytes (setDecodedValueBytes I)))
  simpa [setDecodedValueBytes] using
    decodeCalldata_bytes_some (cd := I.calldata) (x := "value")
      hsz36 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem currentLengthSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem clearCurrentSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem setSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

/-! ## Solm-side string length facts -/

theorem currentLengthResolve (evm : EVM.State) :
    resolveStorageRef? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
  simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, bytesStoreLiteCoreContract, storageDecls, bytesSt, EvalResult.ofOption,
    EvalResult.bind, pure, bind]

theorem currentLengthBodyReturns {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteCoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreLiteCoreContract, locals := ∅ } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure])

theorem currentLengthBodyReverts {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hresolve : resolveStorageRef? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract, locals := ∅ } evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes))
    (hlen : readStorageBytesLength? bytesStoreLiteCoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ currentLengthGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen])))

theorem currentLengthBodyReturnsOfLength {evm : EVM.State} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteCoreConfig evm { base := "current" } = .ok n) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ currentLengthGetter.body
      (.returned { contract := bytesStoreLiteCoreContract, locals := ∅ } evm (some (.int n))) :=
  currentLengthBodyReturns hwv (currentLengthResolve evm) hlen

theorem currentLengthBodyRevertsOfLength {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteCoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ currentLengthGetter.body
      .reverted :=
  currentLengthBodyReverts hwv (currentLengthResolve evm) hlen

theorem clearCurrentBodyRevertsOfRead {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteCoreConfig evm { base := "current" } = .revert) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ clearCurrentTransition.body
      .reverted := by
  have hresolve := currentLengthResolve evm
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.letDeclRevert (by
        rw [evalExpr?, hresolve]
        simp [bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout,
          solidityStorageLayout, readStorageBytesLength?, solidityReadBytesLength?,
          bytesStoreLiteCoreLayout, bind] at hlen
        have hdecode :
            solidityDecodeBytesLengthHeader
              (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) = .revert := by
          cases h :
              solidityDecodeBytesLengthHeader
                (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) <;>
            simp [h, storageNatResultToEval] at hlen
          rfl
        simp [readStorage?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout,
          solidityStorageLayout, solidityReadValue?, solidityReadBytesValue?,
          solidityBytesBaseSlotAndLength?, storageValueResultToEval,
          bytesStoreLiteCoreLayout, hdecode, EvalResult.bind, bind])))

theorem clearCurrentBodyReturnsZero {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreLiteCoreConfig { contract := bytesStoreLiteCoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes ByteArray.empty))
    (hdel :
      deleteStorage? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evm' (some (.int 0))) := by
  let solm1 : Frame :=
    { contract := bytesStoreLiteCoreContract,
      locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hret :
      evalExpr? bytesStoreLiteCoreConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int 0) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem clearCurrentBodyReturnsBytes {evm evm' : EVM.State} {copy : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? bytesStoreLiteCoreConfig { contract := bytesStoreLiteCoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy))
    (hdel :
      deleteStorage? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm currentRef = .ok evm') :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm ∅ clearCurrentTransition.body
      (.returned
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evm' (some (.int copy.size))) := by
  let solm1 : Frame :=
    { contract := bytesStoreLiteCoreContract,
      locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hret :
      evalExpr? bytesStoreLiteCoreConfig solm1 evm'
        (.arrayLength .localVar { base := "copy" }) = .ok (.int copy.size) := by
    simp [solm1, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hread) <|
        ExecBlock.consNormal (ExecStmt.delete (by simpa [solm1] using hdel)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem setBodyReturns {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignCurrent :
      assignStorageRef? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evm .storage currentRef (.bytes value) =
          .ok ({ contract := bytesStoreLiteCoreContract
                 locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) },
              evmCurrent)) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreLiteCoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteCoreContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreLiteCoreContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreLiteCoreConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreLiteCoreConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? bytesStoreLiteCoreConfig solm1 evmCurrent (.arrayLength .localVar { base := "copy" }) =
        .ok (.int value.size) := by
    simp [solm1, locals1, locals0, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consNormal (ExecStmt.assign hcopy (by simpa [solm1, locals1, locals0] using hassignCurrent)) <|
          ExecBlock.consReturn (ExecStmt.return hret)

theorem assignCurrentOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwrite : writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    assignStorageRef? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract
        locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
      evm .storage currentRef (.bytes value) =
        .ok
          ({ contract := bytesStoreLiteCoreContract
             locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
               (.bytes value) },
           evmCurrent) := by
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy"
            (.bytes value) }
        evm currentRef = .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem setBodyReturnsOfWrite {evm evmCurrent : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evmCurrent) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := bytesStoreLiteCoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent (some (.int value.size))) := by
  exact setBodyReturns (evm := evm) (evmCurrent := evmCurrent) (value := value)
    hwv (assignCurrentOfWrite hwrite)

theorem setRuntimeOfWriteAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteCoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreLiteCoreConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmCurrent.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmCurrent.accountMap)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := setBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

theorem setRuntimeOfWriteEVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmEvm evmCurrent : EVM.State}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteCoreContract I.calldata = some setTransition)
    (hdec : decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bytes value)))
    (hwrite : writeStorage? bytesStoreLiteCoreConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "current", steps := [] } .bytes (.bytes value) = .ok evmCurrent)
    (hCreated : acc.1 = evmEvm.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmEvm.accountMap)
    (hState : EVMStateEquiv evmEvm evmCurrent)
    (henc : returnEquiv o (some (.int value.size)) setTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := setBodyReturnsOfWrite
    (evm := evmSolm0) (evmCurrent := evmCurrent) (value := value)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hret.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
    hCreated hAccounts hState henc

theorem setBodyRevertsOfWrite {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body .reverted := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := bytesStoreLiteCoreContract, locals := locals0 }
  let solm1 : Frame := { contract := bytesStoreLiteCoreContract, locals := locals1 }
  have hvalue : evalExpr? bytesStoreLiteCoreConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? bytesStoreLiteCoreConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig solm1 evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm1, locals1, locals0]
  have hassign :
      assignStorageRef? bytesStoreLiteCoreConfig solm1 evm .storage currentRef (.bytes value) =
        .revert := by
    simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consRevert (ExecStmt.assignStoreRevert hcopy hassign)

/-! ## Solidity string length decoding helpers -/

def currentLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

theorem slt_zero_of_left_low_right_high {a b : UInt256}
    (ha : a.toNat < 2 ^ 255) (hb : 2 ^ 255 ≤ b.toNat) :
    UInt256.slt a b = ⟨0⟩ :=
  slt_zero_low_high ha hb

theorem currentLengthBaseSlot {evm : EVM.State} :
    ∃ loc, bytesStoreLiteCoreLayout { base := "current", steps := [.length] } evm =
      some loc ∧ loc.slot = ⟨0⟩ := by
  refine ⟨bytesLikeLengthLoc ⟨0⟩ evm, ?_, by simp⟩
  simp [bytesStoreLiteCoreLayout]

theorem deleteCurrentShortZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    deleteStorage? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract,
        locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteCoreContract, locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm]
  exact deleteSolidityBytesShortZero
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) rfl hresolve currentLengthBaseSlot hload

theorem deleteCurrentShortPacked {evm : EVM.State} {header len : UInt256} {copy : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract,
        locals := (∅ : Store).insert "copy" (.bytes copy) }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteCoreContract, locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm]
  exact deleteSolidityBytesShortPacked
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl hresolve currentLengthBaseSlot hload hpacked hflag hlen hvalid

theorem deleteCurrentLongPrepared {evm : EVM.State} {header len : UInt256} {copy : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract,
        locals := (∅ : Store).insert "copy" (.bytes copy) }
      evm currentRef =
        .ok (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
          ⟨0⟩ 0 ((len.toNat + 31) / 32)) := by
  let solm : Frame :=
    { contract := bytesStoreLiteCoreContract, locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm]
  exact deleteSolidityBytesLongPrepared
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl hresolve currentLengthBaseSlot hload hflag hlen hvalid

theorem writeCurrentShortPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl currentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem writeCurrentShortFromLongPrepared {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 ((len.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0
            ((len.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨0⟩ (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl currentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem writeCurrentLongPacked {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm ⟨0⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨0⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl currentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem writeCurrentLongPackedAbsent {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .ok evm := by
  exact writeSolidityBytesLongPackedAbsent
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl currentLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid hmissing

theorem writeCurrentLongFromLongPrepared {evm : EVM.State} {header len : UInt256}
    {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
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
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len) (value := value)
    rfl currentLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem writeCurrentMalformedLong {evm : EVM.State} {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  have hbase :
      ∃ loc, bytesStoreLiteCoreLayout { base := "current", steps := [.length] } evm =
        some loc ∧ loc.slot = ⟨0⟩ := by
    refine ⟨bytesLikeLengthLoc ⟨0⟩ evm, ?_, by simp⟩
    simp [bytesStoreLiteCoreLayout]
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl hbase hload hflag hbad

theorem writeCurrentMalformedShort {evm : EVM.State} {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes value) = .revert := by
  have hbase :
      ∃ loc, bytesStoreLiteCoreLayout { base := "current", steps := [.length] } evm =
        some loc ∧ loc.slot = ⟨0⟩ := by
    refine ⟨bytesLikeLengthLoc ⟨0⟩ evm, ?_, by simp⟩
    simp [bytesStoreLiteCoreLayout]
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (value := value)
    rfl hbase hload hflag hbad

theorem writeCurrentEmptyFromZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    writeStorage? bytesStoreLiteCoreConfig evm { base := "current", steps := [] }
      .bytes (.bytes ByteArray.empty) =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  exact writeSolidityBytesEmptyFromZero
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (evm := evm) (er := { base := "current", steps := [] }) (baseSlot := ⟨0⟩)
    rfl currentLengthBaseSlot hload

theorem assignCurrentEmptyFromZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    assignStorageRef? bytesStoreLiteCoreConfig
      { contract := bytesStoreLiteCoreContract
        locals := ((∅ : Store).insert "value" (.bytes ByteArray.empty)).insert "copy"
          (.bytes ByteArray.empty) }
      evm .storage currentRef (.bytes ByteArray.empty) =
        .ok
          ({ contract := bytesStoreLiteCoreContract
             locals := ((∅ : Store).insert "value" (.bytes ByteArray.empty)).insert "copy"
               (.bytes ByteArray.empty) },
           Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  let solm : Frame :=
    { contract := bytesStoreLiteCoreContract
      locals := ((∅ : Store).insert "value" (.bytes ByteArray.empty)).insert "copy"
        (.bytes ByteArray.empty) }
  have hresolve :
      resolveStorageRef? bytesStoreLiteCoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
      storageTypeAt?, bytesStoreLiteCoreConfig, bytesStoreLiteCoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm]
  exact assignSolidityBytesEmptyFromZero
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) rfl hresolve currentLengthBaseSlot hload

theorem setLengthWord_eq_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) =
      calldataWord cd (4 + (calldataWord cd 4).toNat) := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have haddr :
      (((⟨4⟩ : UInt256) + calldataWord cd 4).toNat) =
        4 + (calldataWord cd 4).toNat := by
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt (by
      have hsize : 4 + (calldataWord cd 4).toNat < UInt256.size := by
        have hsmall : 4 + (calldataWord cd 4).toNat ≤ 18446744073709551619 := by
          omega
        exact lt_of_le_of_lt hsmall (by norm_num [UInt256.size])
      simpa [Nat.add_comm] using hsize)
  simp [calldataWord, haddr]

theorem setDecodedValueBytes_size_ne_zero {I : ExecutionEnv}
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩) :
    (setDecodedValueBytes I).size ≠ 0 := by
  rw [setDecodedValueBytes_size hpayload]
  intro hzero
  apply hnonzero
  rw [setLengthWord_eq_abi I.calldata hoffMax]
  exact uint256_toNat_eq_zero hzero

theorem setStartPlus31_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩).toNat =
      4 + (calldataWord cd 4).toNat + 31 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 31)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 31 < 2 ^ 255)))

theorem setStart_slt_one
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hsizeSign : cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨1⟩ := by
  apply slt_lit_one_low hsizeSign
  rw [setStartPlus31_toNat cd hoffMax]
  omega

theorem setStart_slt_zero_of_size_high
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hsize : cd.size < UInt256.size)
    (hsizeSign : ¬ cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  apply slt_zero_of_left_low_right_high
  · rw [setStartPlus31_toNat cd hoffMax]
    norm_num [ABI.solcMaxU64] at hoffLeMax ⊢
    omega
  · rw [ulit_toNat' cd.size hsize]
    omega

theorem setPayloadStart_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩).toNat =
      4 + (calldataWord cd 4).toNat + 32 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 32)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 32 < 2 ^ 255)))

theorem setAddZero_toNat (w : UInt256) :
    ((w + ⟨0⟩ : UInt256).toNat) = w.toNat := by
  rw [uadd_toNat]
  simp only [UInt256.toNat]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem setUInt256Mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = a.toNat * b.toNat % UInt256.size :=
  rfl

theorem setLengthMaxWord_zero
    (cd : ByteArray)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [hlenZero]
  native_decide

theorem setPayloadWord_zero
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hmul :
      UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩ =
        ⟨0⟩ := by
    rw [hlenZero]
    native_decide
  apply ugt_zero
  rw [hmul]
  rw [setAddZero_toNat]
  rw [setPayloadStart_toNat cd hoffMax]
  rw [ulit_toNat' cd.size hsize]
  exact hlenWord

theorem setPayloadShort_size_lt
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hpayloadList :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    cd.size < 4 + (calldataWord cd 4).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hltRemain : cd.size - (4 + (off + 32)) < n := by
    by_contra hnot
    have hge : n ≤ cd.size - (4 + (off + 32)) := Nat.le_of_not_gt hnot
    apply hpayloadList
    have : (((cd.toList.drop 4).drop (off + 32)).take n).length = n := by
      rw [htakeLen, min_eq_left hge]
    simpa [off, n] using this
  omega

theorem setPayloadStartLen_le_of_payload
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    4 + (calldataWord cd 4).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ cd.size := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hnle : n ≤ cd.size - (4 + (off + 32)) := by
    by_contra hnot
    have hlt : cd.size - (4 + (off + 32)) < n := Nat.lt_of_not_ge hnot
    have hmin : min n (cd.size - (4 + (off + 32))) = cd.size - (4 + (off + 32)) :=
      min_eq_right (le_of_lt hlt)
    have hpayload' :
        (((cd.toList.drop 4).drop (off + 32)).take n).length = n := by
      simpa [off, n] using hpayload
    rw [htakeLen, hmin] at hpayload'
    omega
  omega

theorem setPayloadWord_zero_of_payload
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨0⟩ := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have hpayloadLe :
      4 + off + 32 + n ≤ cd.size := by
    simpa [off, n, Nat.add_assoc] using
      setPayloadStartLen_le_of_payload cd hlenWord hpayload
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩).toNat = n := by
    rw [setLengthWord_eq_abi cd hoffMax]
    rw [setUInt256Mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [setPayloadStart_toNat cd hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hpayloadLe hsize)
  apply ugt_zero
  rw [hpayloadEndToNat, ulit_toNat' cd.size hsize]
  exact hpayloadLe

theorem setPayloadWord_one_of_payload_short
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayloadList :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨1⟩ := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have hpayloadShortNat :
      cd.size < 4 + off + 32 + n := by
    simpa [off, n, Nat.add_assoc] using
      setPayloadShort_size_lt cd hlenWord hpayloadList
  have hoffLeMax : off ≤ ABI.solcMaxU64 := by
    simpa [off] using Nat.le_of_not_gt hoffMax
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩).toNat = n := by
    rw [setLengthWord_eq_abi cd hoffMax]
    rw [setUInt256Mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [setPayloadStart_toNat cd hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (by
      apply lt_size_of_lt_sign
      norm_num [ABI.solcMaxU64] at hoffLeMax hnLeMax ⊢
      omega)
  apply ugt_one
  rw [hpayloadEndToNat, ulit_toNat' cd.size hsize]
  exact hpayloadShortNat

theorem setLengthMaxWord_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [setLengthWord_eq_abi cd hoffMax]
  apply ugt_zero
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
  exact Nat.le_of_not_gt hlenMax

theorem setLengthMaxWord_one_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨1⟩ := by
  rw [setLengthWord_eq_abi cd hoffMax]
  apply ugt_one
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
  exact hlenHuge

theorem currentLengthHeaderWord_eq_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    currentLengthHeaderWord σ_evm I = currentLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩

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

noncomputable def setMalformedPanicMem1 : ByteArray :=
  solcPanicSelectorWord.toByteArray.write 0 currentLengthZeroReturnMem 0 32

noncomputable def setMalformedPanicMem : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 setMalformedPanicMem1 4 32

noncomputable def setMalformedPanicMem1Of (mem : ByteArray) : ByteArray :=
  solcPanicSelectorWord.toByteArray.write 0 mem 0 32

noncomputable def setMalformedPanicMemOf (mem : ByteArray) : ByteArray :=
  (⟨34⟩ : UInt256).toByteArray.write 0 (setMalformedPanicMem1Of mem) 4 32

noncomputable def setEmptyReturnMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 currentLengthZeroReturnMem 160 32

def currentLengthAllocSize (len : UInt256) : UInt256 :=
  ⟨32⟩ + (((⟨31⟩ + len) / ⟨32⟩) * ⟨32⟩)

def currentLengthFreePtr (len : UInt256) : UInt256 :=
  ⟨128⟩ + currentLengthAllocSize len

noncomputable def currentLengthAllocMem (len : UInt256) : ByteArray :=
  (currentLengthFreePtr len).toByteArray.write 0 solcFreePtrMem 64 32

noncomputable def currentLengthMem (len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (currentLengthAllocMem len) 128 32

def currentLengthPayloadWord (header : UInt256) : UInt256 :=
  (header / ⟨256⟩) * ⟨256⟩

noncomputable def currentLengthPayloadMem (len header : UInt256) : ByteArray :=
  (currentLengthPayloadWord header).toByteArray.write 0 (currentLengthMem len) 160 32

noncomputable def currentLengthPayloadReturnMem (len header : UInt256) : ByteArray :=
  len.toByteArray.write 0 (currentLengthPayloadMem len header) 192 32

theorem currentLengthAllocMem_size (len : UInt256) : (currentLengthAllocMem len).size = 96 := by
  exact solcBytesReturnAllocMem_size len

theorem currentLengthMem_size (len : UInt256) : (currentLengthMem len).size = 160 := by
  exact solcBytesReturnLengthMem_size len

theorem currentLengthMem_read128 (len : UInt256) :
    (currentLengthMem len).readWithPadding 128 32 = UInt256.toByteArray len := by
  exact solcBytesReturnLengthMem_read128 len

theorem currentLengthAllocMem_read64 (len : UInt256) :
    (currentLengthAllocMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesReturnAllocMem_read64 len

theorem currentLengthMem_read64 (len : UInt256) :
    (currentLengthMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesReturnLengthMem_read64 len

theorem currentLengthPayloadMem_read128 (len header : UInt256) :
    (currentLengthPayloadMem len header).readWithPadding 128 32 = UInt256.toByteArray len := by
  exact solcBytesReturnPayloadMem_read128 len (currentLengthPayloadWord header)

theorem currentLengthPayloadMem_size (len header : UInt256) :
    (currentLengthPayloadMem len header).size = 192 := by
  exact solcBytesReturnPayloadMem_size len (currentLengthPayloadWord header)

theorem currentLengthPayloadMem_read64 (len header : UInt256) :
    (currentLengthPayloadMem len header).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesReturnPayloadMem_read64 len (currentLengthPayloadWord header)

theorem currentLengthPayloadMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
  exact solcBytesReturnPayloadMem_mload64 len (currentLengthPayloadWord header) freePtr
    (UInt256.ofNat 6) hfree (by decide)

theorem currentLengthPayloadMem_mload128 (len header : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (currentLengthPayloadMem len header).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadMem len header).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        len := by
  exact solcBytesReturnPayloadMem_mload128 len (currentLengthPayloadWord header)
    (UInt256.ofNat 6) (by decide)

theorem currentLengthPayloadReturnMem_size (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).size = 224 := by
  exact solcBytesReturnPayloadReturnMem_size len (currentLengthPayloadWord header)

theorem currentLengthPayloadReturnMem_read64 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesReturnPayloadReturnMem_read64 len (currentLengthPayloadWord header)

theorem currentLengthPayloadReturnMem_mload64 (len header freePtr : UInt256)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (currentLengthPayloadReturnMem len header).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthPayloadReturnMem len header).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact solcBytesReturnPayloadReturnMem_mload64 len (currentLengthPayloadWord header) freePtr
    (UInt256.ofNat 7) hfree (by decide)

theorem currentLengthPayloadReturnMem_read192 (len header : UInt256) :
    (currentLengthPayloadReturnMem len header).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  exact solcBytesReturnPayloadReturnMem_read192 len (currentLengthPayloadWord header)

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
  exact solcBytesReturnFreePtr_eq_192_of_short_nonzero hnonzero hlt32

theorem readCurrentShortPackedExists {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray,
      evalExpr? bytesStoreLiteCoreConfig { contract := bytesStoreLiteCoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy) ∧ copy.size = len.toNat := by
  exact evalSolidityBytesShortPackedExists
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := { contract := bytesStoreLiteCoreContract, locals := ∅ })
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl (currentLengthResolve evm) currentLengthBaseSlot hload hflag hlen hvalid

theorem readCurrentLongExists {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray,
      evalExpr? bytesStoreLiteCoreConfig { contract := bytesStoreLiteCoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy) ∧ copy.size = len.toNat := by
  exact evalSolidityBytesLongExists
    (cfg := bytesStoreLiteCoreConfig) (layout := bytesStoreLiteCoreLayout)
    (solm := { contract := bytesStoreLiteCoreContract, locals := ∅ })
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl (currentLengthResolve evm) currentLengthBaseSlot hload hflag hlen hvalid

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

theorem currentLengthZeroReturnMem_read128 :
    currentLengthZeroReturnMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [currentLengthZeroReturnMem]
  rw [write32_read_below (UInt256.toByteArray ⟨0⟩) currentLengthZeroMem 160 128
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroMem_size])
    (by decide)]
  exact currentLengthZeroMem_read128

theorem currentLengthZeroReturnMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ currentLengthZeroReturnMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (currentLengthZeroReturnMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨0⟩ : UInt256))
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        currentLengthZeroReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      currentLengthZeroReturnMem_read128)

theorem setEmptyReturnMem_size : setEmptyReturnMem.size = 192 := by
  rw [setEmptyReturnMem,
    write32_eq (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 160
      (by rw [toByteArray_size])
      (by rw [currentLengthZeroReturnMem_size]; decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    currentLengthZeroReturnMem_size]
  omega

theorem setEmptyReturnMem_read64 :
    setEmptyReturnMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [setEmptyReturnMem]
  rw [write32_read_below (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 160 64
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroReturnMem_size]; decide)
    (by decide)]
  exact currentLengthZeroReturnMem_read64

theorem setEmptyReturnMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ setEmptyReturnMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (setEmptyReturnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, setEmptyReturnMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      setEmptyReturnMem_read64)

theorem setEmptyReturnMem_read160 :
    setEmptyReturnMem.readWithPadding 160 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [setEmptyReturnMem]
  rw [write32_read_back (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 160
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroReturnMem_size]; decide)]
  rw [toByteArray_extract_all]

/-! ## Shared runtime revert paths -/

theorem bytesStoreLiteCoreBodyReverts_nonPayable (t : TransitionDecl)
    (ht : t ∈ bytesStoreLiteCoreContract.transitions) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evm locals t.body .reverted := by
  simp [bytesStoreLiteCoreContract] at ht
  rcases ht with rfl | rfl | rfl <;> exact bodyReverts_nonPayable h

theorem bytesStoreLiteCoreX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt bytesStoreLiteCoreBytecode)
    (opC := solcGuardTgtOp bytesStoreLiteCoreBytecode)
    (wC := solcGuardTgtWidth bytesStoreLiteCoreBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem bytesStoreLiteCoreX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt bytesStoreLiteCoreBytecode)
    (opC := solcGuardTgtOp bytesStoreLiteCoreBytecode)
    (wC := solcGuardTgtWidth bytesStoreLiteCoreBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc bytesStoreLiteCoreBytecode)
    (rtgt := solcCalldataRevertTgt bytesStoreLiteCoreBytecode)
    (opR := solcCalldataRevertTgtOp bytesStoreLiteCoreBytecode)
    (wR := solcCalldataRevertTgtWidth bytesStoreLiteCoreBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem bytesStoreLiteCoreX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 3 → (bytesStoreLiteCoreSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat bytesStoreLiteCoreBytecode
          (nthArmPc bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc j))
        (bytesStoreLiteCoreSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hmiss : (bytesStoreLiteCoreArmSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteCoreArmSelBytes, bytesStoreLiteCoreSelBytes] using hnm 0 (by omega)
      rw [bytesStoreLiteCoreArmEq I hsz 0 (by decide), hmiss]
      rfl
    · have hmiss : (bytesStoreLiteCoreArmSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteCoreArmSelBytes, bytesStoreLiteCoreSelBytes] using hnm 2 (by omega)
      rw [bytesStoreLiteCoreArmEq I hsz 1 (by decide), hmiss]
      rfl
    · have hmiss : (bytesStoreLiteCoreArmSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [bytesStoreLiteCoreArmSelBytes, bytesStoreLiteCoreSelBytes] using hnm 1 (by omega)
      rw [bytesStoreLiteCoreArmEq I hsz 2 (by decide), hmiss]
      rfl
  have hprefix : solcDispatchPrefixWellFormed bytesStoreLiteCoreBytecode bytesStoreLiteCoreFirstArmPc := by
    solc_dispatch_prefix
  obtain ⟨_, _, h30⟩ := solcDispatchReachSelector
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (code := bytesStoreLiteCoreBytecode) (firstPc := bytesStoreLiteCoreFirstArmPc)
    hcode hwv hsz hsize hprefix (by jump_dest)
  have h41 := h30.selectorArmNotTakenAuto
    (bytesStoreLiteCoreArmsWellFormed 0 (by decide)) (heq0 0 (by decide)) (by simp)
  have h52 := h41.selectorArmNotTakenAuto
    (by simpa [nthArmPc] using bytesStoreLiteCoreArmsWellFormed 1 (by decide))
    (by simpa [nthArmPc] using heq0 1 (by decide)) (by simp)
  have h63 := h52.selectorArmNotTakenAuto
    (by simpa [nthArmPc] using bytesStoreLiteCoreArmsWellFormed 2 (by decide))
    (by simpa [nthArmPc] using heq0 2 (by decide)) (by simp)
  have h63' : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨63⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteCoreFirstArmPc, nthArmPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h63⟩
  obtain ⟨_, _, h63rd⟩ := h63'
  have h64 := h63rd.jumpdest (by decide) (by simp)
  exact h64.revertStub (by decide) (by decide) (by decide) (by simp)

theorem bytesStoreLiteCoreNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (bytesStoreLiteCoreX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg bytesStoreLiteCoreContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ bytesStoreLiteCoreContract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (bytesStoreLiteCoreBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem bytesStoreLiteCoreShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (bytesStoreLiteCoreX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch
    hcode (bytesStoreLiteCoreDispatch_none_short hsz)

theorem bytesStoreLiteCoreNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 3 → (bytesStoreLiteCoreSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (bytesStoreLiteCoreX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (bytesStoreLiteCoreDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (bytesStoreLiteCoreX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (bytesStoreLiteCoreDispatch_none_short hshort)

/-! ## `currentLength()` EVM paths -/

theorem bytesStoreLiteCoreX_currentLengthReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      [currentLengthHeaderWord σ I, ⟨286⟩, ⟨0⟩, ⟨0⟩, ⟨123⟩,
        bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd115⟩ := hreach
  have rd273 := evm_run rd115 with [
    jumpdest, push2 ⟨123⟩, push2 ⟨273⟩, jump (by jump_dest)]
  have rd277 := evm_run rd273 with [
    jumpdest, push0, push0, dup1]
  obtain ⟨_, _, rd278₀⟩ := rd277.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd278⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨278⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨123⟩, bytesStoreLiteCoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd278₀⟩
  exact ⟨_, _, evm_run rd278 with [
    push2 ⟨286⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_bytesLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd911 := rd903.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd911 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteCoreX_bytesLengthDecoderLongValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd911 := rd903.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd911 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteCoreX_bytesLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd911 := rd903.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd911 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd911 := rd903.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd911 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteCoreX_currentLengthDecoderLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨286⟩
      [UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨123⟩,
        bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteCoreX_bytesLengthDecoderLongValid
    (bytesStoreLiteCoreX_currentLengthReachDecoder hreach) hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_currentLengthDecoderShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨286⟩
      [UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩,
        ⟨0⟩, ⟨0⟩, ⟨123⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact bytesStoreLiteCoreX_bytesLengthDecoderShortValid
    (bytesStoreLiteCoreX_currentLengthReachDecoder hreach) hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_currentLengthReturnFromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hdecoded : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨286⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨123⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd286⟩ := hdecoded
  have rd123 := evm_run rd286 with [
    jumpdest, swap1, pop, swap1, pop, swap1, jump (by jump_dest)]
  have rd744 := evm_run rd123 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨136⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem len) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (((⟨128⟩ : UInt256) + ⟨0⟩).toNat) = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd136 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd136 with [
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

theorem bytesStoreLiteCoreX_currentLengthLongValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)) := by
  exact bytesStoreLiteCoreX_currentLengthReturnFromDecoded
    (bytesStoreLiteCoreX_currentLengthDecoderLongValid hreach hflag hvalid)

theorem bytesStoreLiteCoreX_currentLengthShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)) := by
  exact bytesStoreLiteCoreX_currentLengthReturnFromDecoded
    (bytesStoreLiteCoreX_currentLengthDecoderShortValid hreach hflag hvalid)

theorem bytesStoreLiteCoreX_currentLengthMalformedPanic {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨903⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd903⟩ := hreach
  have rd824 := evm_run rd903 with [
    push2 ⟨910⟩, push2 ⟨824⟩, jump (by jump_dest)]
  have rd825 := rd824.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd858 := rd825.pushConst solcPanicSelectorWord (width := 32)
    (op := Operation.POp.PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd858 with [
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

theorem bytesStoreLiteCoreX_setMalformedPanic {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨903⟩ stk
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd903⟩ := hreach
  have rd824 := evm_run rd903 with [
    push2 ⟨910⟩, push2 ⟨824⟩, jump (by jump_dest)]
  have rd825 := rd824.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd858 := rd825.pushConst solcPanicSelectorWord (width := 32)
    (op := Operation.POp.PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd858 with [
    push0,
    raw mstore 0 setMalformedPanicMem1 (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 setMalformedPanicMem (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by simp only [List.length_cons]; omega)]

theorem bytesStoreLiteCoreX_bytesLengthDecoderLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_currentLengthMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_bytesLengthDecoderShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_currentLengthMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_bytesLengthDecoderLongMalformedSetMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_setMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_bytesLengthDecoderShortMalformedSetMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_setMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_currentLengthLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := bytesStoreLiteCoreX_currentLengthReachDecoder hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest) (by evm_ov)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad (by evm_ov)
  exact bytesStoreLiteCoreX_currentLengthMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_currentLengthShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨115⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := bytesStoreLiteCoreX_currentLengthReachDecoder hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag (by evm_ov)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad (by evm_ov)
  exact bytesStoreLiteCoreX_currentLengthMalformedPanic ⟨_, _, rd903'⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_clearCurrentReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      [currentLengthHeaderWord σ I, ⟨307⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
        bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd145⟩ := hreach
  have rd293 := evm_run rd145 with [
    jumpdest, push2 ⟨153⟩, push2 ⟨293⟩, jump (by jump_dest)]
  have rd298 := evm_run rd293 with [
    jumpdest, push0, push0, push0, dup1]
  obtain ⟨_, _, rd299₀⟩ := rd298.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd299⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨299⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd299₀⟩
  exact ⟨_, _, evm_run rd299 with [
    push2 ⟨307⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteCoreX_bytesLengthDecoderLongMalformed
    (hreach := bytesStoreLiteCoreX_clearCurrentReachDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨307⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_clearCurrentShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact bytesStoreLiteCoreX_bytesLengthDecoderShortMalformed
    (hreach := bytesStoreLiteCoreX_clearCurrentReachDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨307⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_setDecoderHeadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hshort : I.calldata.size < 36) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨666⟩, push2 ⟨540⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_setDecoderHeadHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨666⟩, push2 ⟨540⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_setDecoderOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd681 with [
    dup2,
    gt, iszero, push2 ⟨696⟩,
    jumpiNT (by rw [hgt']; decide),
    push2 ⟨695⟩, push2 ⟨544⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_stringDecoder560LengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨560⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨581⟩,
    jumpiNT (by exact hstart),
    push2 ⟨580⟩, push2 ⟨548⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_stringDecoder560LengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨560⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd581 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨581⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd595 := RD.pushConst (evm_run rd581 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd595 with [
    dup2, gt, iszero, push2 ⟨610⟩,
    jumpiNT (by rw [hlenMax]; decide),
    push2 ⟨609⟩, push2 ⟨552⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_stringDecoder560PayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨560⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt ((start + ⟨32⟩) +
          UInt256.mul (uInt256OfByteArray (I.calldata.readBytes start.toNat 32)) ⟨1⟩)
        ennd = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd581 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨581⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd595 := RD.pushConst (evm_run rd581 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd595 with [
    dup2, gt, iszero, push2 ⟨610⟩,
    jumpiT (by rw [hlenMax]; decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨1⟩, dup3, mul, dup4, add, gt, iszero, push2 ⟨638⟩,
    jumpiNT (by rw [hpayload]; decide),
    push2 ⟨637⟩, push2 ⟨556⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem bytesStoreLiteCoreX_stringDecoder560Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨560⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt ((start + ⟨32⟩) +
          UInt256.mul (uInt256OfByteArray (I.calldata.readBytes start.toNat 32)) ⟨1⟩)
        ennd = ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD bytesStoreLiteCoreBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (uInt256OfByteArray (I.calldata.readBytes start.toNat 32) ::
        (start + ⟨32⟩) :: headOff :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd581 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨581⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd595 := RD.pushConst (evm_run rd581 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd638 := evm_run rd595 with [
    dup2, gt, iszero, push2 ⟨610⟩,
    jumpiT (by rw [hlenMax]; decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨1⟩, dup3, mul, dup4, add, gt, iszero, push2 ⟨638⟩,
    jumpiT (by rw [hpayload]; decide) (by jump_dest)]
  exact ⟨_, _, by
    simpa using
      (evm_run rd638 with [
        jumpdest, swap3, pop, swap3, swap1, pop, jump hret])⟩

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteCoreX_setDecoderLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLeMax : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord I.calldata 4).toNat < 2 ^ 255 := by
    omega
  have hstart31ToNat :
      ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩).toNat) =
        4 + (calldataWord I.calldata 4).toNat + 31 := by
    have hoffSize : (calldataWord I.calldata 4).toNat < UInt256.size :=
      (calldataWord I.calldata 4).val.isLt
    have hoffOfNat :
        (UInt256.ofNat (calldataWord I.calldata 4).toNat).toNat =
          (calldataWord I.calldata 4).toNat :=
      ulit_toNat' _ hoffSize
    rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
      (b := (calldataWord I.calldata 4).toNat)
      (c := 31)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign hoffSmall)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : 4 + (calldataWord I.calldata 4).toNat < 2 ^ 255))
      (lt_size_of_lt_sign (by omega :
        4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255)))
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [hstart31ToNat]
        omega
      · rw [hstart31ToNat]
        omega
    · apply slt_zero_of_left_low_right_high
      · rw [hstart31ToNat]
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd696 := evm_run rd681 with [
    dup2, gt, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd560 := evm_run rd696 with [
    jumpdest, push2 ⟨708⟩, dup6, dup3, dup7, add, push2 ⟨560⟩,
    jump (by jump_dest)]
  exact bytesStoreLiteCoreX_stringDecoder560LengthShort rd560
    (by simpa [calldataWord] using hstart) (by evm_ov)

theorem bytesStoreLiteCoreX_setDecoderSignedStartHigh {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeSign : ¬ I.calldata.size < 2 ^ 255) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setStart_slt_zero_of_size_high I.calldata hoffMax hsize hsizeSign
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd696 := evm_run rd681 with [
    dup2, gt, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd560 := evm_run rd696 with [
    jumpdest, push2 ⟨708⟩, dup6, dup3, dup7, add, push2 ⟨560⟩,
    jump (by jump_dest)]
  exact bytesStoreLiteCoreX_stringDecoder560LengthShort rd560
    (by simpa [calldataWord] using hstart) (by evm_ov)

theorem bytesStoreLiteCoreX_setDecoderLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd696 := evm_run rd681 with [
    dup2, gt, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd560 := evm_run rd696 with [
    jumpdest, push2 ⟨708⟩, dup6, dup3, dup7, add, push2 ⟨560⟩,
    jump (by jump_dest)]
  exact bytesStoreLiteCoreX_stringDecoder560LengthHuge rd560
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by evm_ov)

theorem bytesStoreLiteCoreX_setDecoderPayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd696 := evm_run rd681 with [
    dup2, gt, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd560 := evm_run rd696 with [
    jumpdest, push2 ⟨708⟩, dup6, dup3, dup7, add, push2 ⟨560⟩,
    jump (by jump_dest)]
  exact bytesStoreLiteCoreX_stringDecoder560PayloadShort rd560
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by simpa [calldataWord] using hpayload)
    (by evm_ov)

theorem bytesStoreLiteCoreX_setDecoderOkCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨175⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteCoreReachSetDecoder
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
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd671 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨667⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd681 := RD.pushConst rd671 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd696 := evm_run rd681 with [
    dup2, gt, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd560 := evm_run rd696 with [
    jumpdest, push2 ⟨708⟩, dup6, dup3, dup7, add, push2 ⟨560⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd708⟩ := bytesStoreLiteCoreX_stringDecoder560Ok rd560
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by simpa [calldataWord] using hpayload)
    (by jump_dest)
    (by evm_ov)
  have rd88 := evm_run rd708 with [
    jumpdest, swap3, pop, swap3, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [calldataWord] using
      (evm_run rd88 with [jumpdest, push2 ⟨175⟩, jump (by jump_dest)])⟩

theorem bytesStoreLiteCore_write_len_zero (src base : ByteArray) (sa da : Nat) :
    src.write sa base da 0 = base := by
  simp [ByteArray.write]

noncomputable def setCalldataMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  cd.write payloadStart.toNat (currentLengthMem len) 160 len.toNat

noncomputable def setPaddedMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (setCalldataMem cd len payloadStart) (((⟨160⟩ : UInt256) + len).toNat) 32

def setHelperEntryAw (len : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (UInt256.ofNat
        (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
      (((⟨160⟩ : UInt256) + len).toNat) 32)

def setHelperPayloadAw (len : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (setHelperEntryAw len).toNat 160 32)

noncomputable def setHelperPayloadWord
    (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  if (⟨160⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size ∨
      (⟨160⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat (fromByteArrayBigEndian
      ((setPaddedMem cd len payloadStart).readWithPadding (⟨160⟩ : UInt256).toNat 32))

def setShortPackedHeader (payloadWord lenWord : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land payloadWord
      (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ lenWord))))
    (UInt256.mul ⟨2⟩ lenWord)

theorem bytesStoreLiteCoreX_setReachStorageWriteMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart : UInt256} {k C : Nat}
    (rd : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
        [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart)
        (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k' C' := by
  have rd219 := evm_run rd with [
    jumpdest, push0, push0, dup4, dup4, dup1, dup1, push1 ⟨31⟩, add,
    push1 ⟨32⟩, dup1, swap2, div, mul, push1 ⟨32⟩, add,
    push1 ⟨64⟩,
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
      (by decide) (by evm_ov),
    dup1, swap4, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5) (by native_decide)
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
  have rd220 := RD.calldatacopy
    (Cₘ awCopy - Cₘ (UInt256.ofNat 5))
    (setCalldataMem I.calldata len payloadStart)
    awCopy
    rd219 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy]
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 from by decide])
    (by
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 from by decide]
      rfl)
    hawCopy
    (by evm_ov)
  have rd224 := evm_run rd220 with [push0, dup2, dup5, add]
  let awPad : UInt256 :=
    UInt256.ofNat (MachineState.M awCopy.toNat (((⟨160⟩ : UInt256) + len).toNat) 32)
  have rd225 := RD.mstore
    (Cₘ awPad - Cₘ awCopy)
    (setPaddedMem I.calldata len payloadStart)
    awPad
    rd224 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy, awPad]
      rw [show ((⟨32⟩ : UInt256) + ⟨128⟩ + len) = ((⟨160⟩ : UInt256) + len) from by
        rw [show ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ from by decide]])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd1350 := evm_run rd225 with [
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, swap1, pop,
    dup1, dup4, add, swap3, pop, pop, pop, pop, pop, pop, pop, swap1, pop,
    dup1, push0, swap1, dup2, push2 ⟨261⟩, swap2, swap1, push2 ⟨1350⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [setCalldataMem, setPaddedMem, setHelperEntryAw, awCopy, awPad,
      currentLengthAllocSize, currentLengthFreePtr] using rd1350⟩

theorem setCalldataMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setCalldataMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  exact solcBytesSetCalldataMem_read128 cd len payloadStart hlen hsrc

theorem setCalldataMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setCalldataMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesSetCalldataMem_read64 cd len payloadStart hlen hsrc

theorem setCalldataMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setCalldataMem cd len payloadStart).size = 160 + len.toNat := by
  exact solcBytesSetCalldataMem_size cd len payloadStart hlen hsrc

set_option maxHeartbeats 800000 in
theorem setCalldataMem_extract_payload
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setCalldataMem cd len payloadStart).extract 160 (160 + len.toNat) =
      cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  exact solcBytesSetCalldataMem_extract_payload cd len payloadStart hlen hsrc

theorem setDataEnd_toNat_of_short {len : UInt256}
    (hshort : len.toNat < 32) :
    (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat := by
  exact solcBytesSetDataEnd_toNat_of_short hshort

theorem setDataEnd_toNat_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat := by
  exact solcBytesSetDataEnd_toNat_of_u64 hlenMax

theorem setPaddedMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (setPaddedMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  exact solcBytesSetPaddedMem_read128 cd len payloadStart hlen hsrc hadd

theorem setPaddedMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (setPaddedMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact solcBytesSetPaddedMem_read64 cd len payloadStart hlen hsrc hadd

theorem setPaddedMem_size_ge160
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    160 ≤ (setPaddedMem cd len payloadStart).size := by
  exact solcBytesSetPaddedMem_size_ge160 cd len payloadStart hlen hsrc hadd

theorem setPaddedMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (setPaddedMem cd len payloadStart).size = 192 + len.toNat := by
  exact solcBytesSetPaddedMem_size cd len payloadStart hlen hsrc hadd

theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq a, ← byteArray_toList_eq b]
  exact h

theorem setDecodedValueBytes_eq_extract {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    setDecodedValueBytes I =
      I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  apply byteArray_eq_of_toList_eq
  rw [setDecodedValueBytes_toList]
  rw [byteArray_toList_eq (I.calldata.extract payloadStart.toNat
    (payloadStart.toNat + len.toNat))]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq I.calldata]
  have hstart :
      payloadStart.toNat = 4 + (calldataWord I.calldata 4).toNat + 32 := by
    rw [hpayloadStart, setPayloadStart_toNat I.calldata hoffMax]
  have hlen :
      len.toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    rw [hlenAbi]
  rw [hstart, hlen]
  rw [List.drop_drop]
  rw [show 4 + ((calldataWord I.calldata 4).toNat + 32) =
      4 + (calldataWord I.calldata 4).toNat + 32 by omega]
  rw [show 4 + (calldataWord I.calldata 4).toNat + 32 +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat -
        (4 + (calldataWord I.calldata 4).toNat + 32) =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat by omega]

set_option maxHeartbeats 800000 in
theorem setPaddedMem_read160_short_toList
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    ((setPaddedMem cd len payloadStart).readWithPadding 160 32).toList =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).toList ++
        List.replicate (32 - len.toNat) 0 := by
  exact solcBytesSetPaddedMem_read160_short_toList cd len payloadStart hnz hshort hsrc

theorem setHelperEntryAw_eq_7_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    setHelperEntryAw len = ⟨7⟩ := by
  apply u256_inj
  dsimp [setHelperEntryAw]
  simp only [MachineState.M]
  rw [setDataEnd_toNat_of_short hshort]
  have hcopy : (160 + len.toNat + 31) / 32 = 6 := by omega
  have hpad : (160 + len.toNat + 32 + 31) / 32 = 7 := by omega
  rw [hcopy, hpad]
  decide

theorem setHelperEntryAw_mload128_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    ¬ (⟨128⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ := by
  rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem set_machineState_M_mul32_lt_of_bounds {s f l : ℕ}
    (hs : s * 32 < UInt256.size)
    (hfl : f + l + 31 < UInt256.size) :
    MachineState.M s f l * 32 < UInt256.size := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl, hs]
  · simp only [MachineState.M]
    let c := (f + l + 31) / 32
    have hceil : ((f + l + 31) / 32) * 32 ≤ f + l + 31 :=
      Nat.div_mul_le_self (f + l + 31) 32
    have hc : c * 32 < UInt256.size := by
      exact lt_of_le_of_lt hceil hfl
    by_cases hsc : s ≤ c
    · rw [max_eq_right hsc]
      exact hc
    · have hcs : c ≤ s := Nat.le_of_not_ge hsc
      rw [max_eq_left hcs]
      exact hs

theorem set_machineState_M_ge_left {s f l : Nat} : s ≤ MachineState.M s f l := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl]
  · simp [MachineState.M]

theorem set_mstoreCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: stk →
      memoryExpansionCost st .MSTORE =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem set_mloadCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: stk →
      memoryExpansionCost st .MLOAD =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem set_revertCostSpec {aw off len : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: len :: stk →
      memoryExpansionCost st .REVERT =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
    List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem set_activeWordsMstore0_eq_self {aw : UInt256} (hge : 1 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 1 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem set_activeWordsMstore4_eq_self {aw : UInt256} (hge : 2 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 4 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 2 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem set_activeWordsMload128_eq_self {aw : UInt256} (hge : 5 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 5 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem set_activeWordsRevert0_36_eq_self {aw : UInt256} (hge : 2 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 36) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 2 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem setHelperEntryAw_ge5_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    5 ≤ (setHelperEntryAw len).toNat := by
  let copyWords := MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat
  have hcopyNoWrap : copyWords * 32 < UInt256.size := by
    dsimp [copyWords]
    apply set_machineState_M_mul32_lt_of_bounds
    · change 5 * 32 < UInt256.size
      norm_num [UInt256.size]
    · have hmax : 160 + ABI.solcMaxU64 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hcopySize : copyWords < UInt256.size := by
    have hle : copyWords ≤ copyWords * 32 := by
      simpa using Nat.mul_le_mul_left copyWords (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hcopyNoWrap
  have hcopyToNat : (UInt256.ofNat copyWords).toNat = copyWords :=
    ulit_toNat' copyWords hcopySize
  have hentryNoWrap :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 <
        UInt256.size := by
    apply set_machineState_M_mul32_lt_of_bounds
    · exact hcopyNoWrap
    · rw [setDataEnd_toNat_of_u64 hlenMax]
      have hmax : 160 + ABI.solcMaxU64 + 32 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hentrySize :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 < UInt256.size := by
    have hle :
        MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 ≤
          MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32)
        (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hentryNoWrap
  dsimp [setHelperEntryAw]
  change 5 ≤
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat copyWords).toNat (((⟨160⟩ : UInt256) + len).toNat)
        32)).toNat
  rw [hcopyToNat, ulit_toNat' _ hentrySize]
  exact le_trans (by
      dsimp [copyWords]
      change 5 ≤ MachineState.M 5 160 len.toNat
      exact set_machineState_M_ge_left)
    (set_machineState_M_ge_left (s := copyWords)
      (f := (((⟨160⟩ : UInt256) + len).toNat)) (l := 32))

theorem setHelperEntryAw_mul32_lt_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    (setHelperEntryAw len).toNat * 32 < UInt256.size := by
  let copyWords := MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat
  have hcopyNoWrap : copyWords * 32 < UInt256.size := by
    dsimp [copyWords]
    apply set_machineState_M_mul32_lt_of_bounds
    · change 5 * 32 < UInt256.size
      norm_num [UInt256.size]
    · have hmax : 160 + ABI.solcMaxU64 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hcopySize : copyWords < UInt256.size := by
    have hle : copyWords ≤ copyWords * 32 := by
      simpa using Nat.mul_le_mul_left copyWords (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hcopyNoWrap
  have hcopyToNat : (UInt256.ofNat copyWords).toNat = copyWords :=
    ulit_toNat' copyWords hcopySize
  have hentryNoWrap :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 <
        UInt256.size := by
    apply set_machineState_M_mul32_lt_of_bounds
    · exact hcopyNoWrap
    · rw [setDataEnd_toNat_of_u64 hlenMax]
      have hmax : 160 + ABI.solcMaxU64 + 32 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hentrySize :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 < UInt256.size := by
    have hle :
        MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 ≤
          MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32)
        (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hentryNoWrap
  dsimp [setHelperEntryAw]
  change
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat copyWords).toNat (((⟨160⟩ : UInt256) + len).toNat)
        32)).toNat * 32 < UInt256.size
  rw [hcopyToNat, ulit_toNat' _ hentrySize]
  exact hentryNoWrap

theorem set_wordMul32_not_le128_of_ge5 {aw : UInt256}
    (hge : 5 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h128 : (⟨128⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h128
  change 128 ≥ aw.toNat * 32 at h128
  nlinarith

theorem set_wordMul32_not_le64_of_ge5 {aw : UInt256}
    (hge : 5 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h64 : (⟨64⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h64
  change 64 ≥ aw.toNat * 32 at h64
  nlinarith

theorem setHelperEntryAw_mload128_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    ¬ (⟨128⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ :=
  set_wordMul32_not_le128_of_ge5
    (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax)
    (setHelperEntryAw_mul32_lt_of_u64 (len := len) hlenMax)

theorem setHelperEntryAw_mload64_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    ¬ (⟨64⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ :=
  set_wordMul32_not_le64_of_ge5
    (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax)
    (setHelperEntryAw_mul32_lt_of_u64 (len := len) hlenMax)

theorem setHelperEntryAw_mload160_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    ¬ (⟨160⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ := by
  rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem setHelperPayloadWord_eq_mload160_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    setHelperPayloadWord cd len payloadStart =
      UInt256.ofNat (fromByteArrayBigEndian
        ((setPaddedMem cd len payloadStart).readWithPadding 160 32)) := by
  unfold setHelperPayloadWord
  rw [if_neg]
  · rfl
  · exact not_or.mpr ⟨
      (by
        have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
        omega),
      setHelperEntryAw_mload160_of_short_nonzero hnz hshort⟩

theorem setHelperPayloadWord_eq_decodedPayloadWord {I : ExecutionEnv}
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
    setHelperPayloadWord I.calldata len payloadStart =
      uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding 0 32) := by
  rw [setHelperPayloadWord_eq_mload160_short_nonzero I.calldata len payloadStart hnz hshort hsrc]
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  apply congrArg fromByteArrayBigEndian
  apply byteArray_eq_of_toList_eq
  rw [setPaddedMem_read160_short_toList I.calldata len payloadStart hnz hshort hsrc]
  rw [setDecodedValueBytes_readWithPadding_short_toList
    (I := I)
    (by simpa [← hlenAbi] using hshort)
    (by simpa [← hlenAbi] using hnz)
    hpayload]
  rw [setDecodedValueBytes_eq_extract hlenAbi hpayloadStart hoffMax]
  rw [show (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat =
      len.toNat by rw [hlenAbi]]

theorem setShortPackedHeader_mask_of_short {len : UInt256}
    (hshort : len.toNat < 32) :
    UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len)) =
      UInt256.ofNat (2 ^ 256 - 2 ^ (256 - 8 * len.toNat)) := by
  let n := len.toNat
  have hlen : len = UInt256.ofNat n := (u256_ofNat_toNat len).symm
  rw [hlen]
  rw [ulit_toNat' n (by
    have : n < 32 := hshort
    norm_num [UInt256.size] at this ⊢
    omega)]
  change UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ (UInt256.ofNat n))) =
    UInt256.ofNat (2 ^ 256 - 2 ^ (256 - 8 * n))
  change n < 32 at hshort
  interval_cases n <;> native_decide

theorem setShortPackedHeader_eq_solidityShortBytesWord {I : ExecutionEnv}
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
    setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len =
      solidityShortBytesWord (setDecodedValueBytes I) := by
  have hpayloadWord :=
    setHelperPayloadWord_eq_decodedPayloadWord (I := I) (len := len)
      (payloadStart := payloadStart) hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload
  have hsize : (setDecodedValueBytes I).size = len.toNat := by
    rw [setDecodedValueBytes_size hpayload]
    rw [hlenAbi]
  have hvalueShort : (setDecodedValueBytes I).size < 32 := by
    rw [hsize]
    exact hshort
  have hvalueNonzero : (setDecodedValueBytes I).size ≠ 0 := by
    rw [hsize]
    exact hnz
  have hlow₀ :=
    uInt256OfByteArray_readWithPadding_zero_low_zero
      (setDecodedValueBytes I) hvalueNonzero hvalueShort
  have hlow :
      (uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding 0 32)).toNat %
        2 ^ (256 - 8 * len.toNat) = 0 := by
    rw [show 256 - 8 * len.toNat = 8 * (32 - (setDecodedValueBytes I).size) by
      rw [hsize]
      omega]
    exact hlow₀
  have htag :
      UInt256.mul ⟨2⟩ len = UInt256.ofNat ((setDecodedValueBytes I).size * 2) := by
    apply u256_inj
    rw [u256_mul_toNat]
    change (2 * len.toNat) % UInt256.size =
      ((setDecodedValueBytes I).size * 2) % UInt256.size
    rw [hsize, Nat.mul_comm]
  rw [setShortPackedHeader, solidityShortBytesWord, hpayloadWord,
    setShortPackedHeader_mask_of_short hshort]
  rw [u256_land_high_mask_eq_self (w :=
    uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding 0 32))
    (k := 256 - 8 * len.toNat) (by omega) hlow]
  rw [htag]

theorem setHelperPayloadAw_eq_7_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    setHelperPayloadAw len = ⟨7⟩ := by
  apply u256_inj
  dsimp [setHelperPayloadAw]
  rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem setPaddedMem_mload128_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size
        ∨ (⟨128⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setPaddedMem cd len payloadStart).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := setHelperEntryAw len) (v := len)
    (by
      have hge := setPaddedMem_size_ge160 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      omega)
    (setHelperEntryAw_mload128_of_short_nonzero hnz hshort)
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        setPaddedMem_read128 cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort))

theorem setPaddedMem_mload128_nonzero_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size
        ∨ (⟨128⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setPaddedMem cd len payloadStart).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := setHelperEntryAw len) (v := len)
    (by
      have hge := setPaddedMem_size_ge160 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      omega)
    (setHelperEntryAw_mload128_of_u64 hlenMax)
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        setPaddedMem_read128 cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax))

theorem setPaddedMem_mload64_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ setHelperPayloadAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setPaddedMem cd len payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setHelperPayloadAw len)
    (v := currentLengthFreePtr len)
    (by
      have hge := setPaddedMem_size_ge160 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      omega)
    (by
      rw [setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort]
      decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        setPaddedMem_read64 cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort))

theorem setPaddedMem_mload64_nonzero_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ setHelperEntryAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setPaddedMem cd len payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setHelperEntryAw len)
    (v := currentLengthFreePtr len)
    (by
      have hge := setPaddedMem_size_ge160 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      omega)
    (setHelperEntryAw_mload64_of_u64 hlenMax)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        setPaddedMem_read64 cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax))

theorem setPaddedMem_mload128_short_nonzero_payloadAw
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setPaddedMem cd len payloadStart).size
        ∨ (⟨128⟩ : UInt256) ≥ setHelperPayloadAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setPaddedMem cd len payloadStart).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := setHelperPayloadAw len) (v := len)
    (by
      have hge := setPaddedMem_size_ge160 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      omega)
    (by
      rw [setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort]
      decide)
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        setPaddedMem_read128 cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort))

noncomputable def setShortReturnMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  len.toByteArray.write 0 (setPaddedMem cd len payloadStart) 192 32

theorem setShortReturnMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setShortReturnMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [setShortReturnMem]
  rw [write32_read_below (UInt256.toByteArray len)
    (setPaddedMem cd len payloadStart) 192 64
    (by rw [toByteArray_size])
    (by
      rw [setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)]
      omega)
    (by decide)]
  exact setPaddedMem_read64 cd len payloadStart hnz hsrc
    (setDataEnd_toNat_of_short hshort)

theorem setShortReturnMem_mload64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setShortReturnMem cd len payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setShortReturnMem cd len payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7)
    (v := currentLengthFreePtr len)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, setShortReturnMem]
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [write32_eq (UInt256.toByteArray len) (setPaddedMem cd len payloadStart) 192
        (by rw [toByteArray_size])
        (by rw [hsize]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, toByteArray_size, hsize]
      omega)
    (by decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        setShortReturnMem_read64 cd len payloadStart hnz hshort hsrc)

theorem setShortReturnMem_read192
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setShortReturnMem cd len payloadStart).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  rw [setShortReturnMem]
  rw [write32_read_back (UInt256.toByteArray len)
    (setPaddedMem cd len payloadStart) 192
    (by rw [toByteArray_size])
    (by
      rw [setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)]
      omega)]
  rw [toByteArray_extract_all]

theorem bytesStoreLiteCoreX_setEmptyReachStorageWrite {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart : UInt256} {k C : Nat}
    (rd : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
        [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
          ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  have rd219 := evm_run rd with [
    jumpdest, push0, push0, dup4, dup4, dup1, dup1, push1 ⟨31⟩, add,
    push1 ⟨32⟩, dup1, swap2, div, mul, push1 ⟨32⟩, add,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 currentLengthZeroAllocMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    dup1, swap4, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 currentLengthZeroMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup4, dup4, dup1, dup3, dup5]
  let awCopy : UInt256 :=
    UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat (⟨160⟩ : UInt256).toNat
      (⟨0⟩ : UInt256).toNat)
  have hawCopy :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat (⟨160⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) = awCopy := by
    rfl
  have rd220 := RD.calldatacopy
    (Cₘ awCopy - Cₘ (UInt256.ofNat 5))
    currentLengthZeroMem
    awCopy
    rd219 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy]
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) =
          (⟨160⟩ : UInt256).toNat by native_decide])
    (by
      simpa using
        bytesStoreLiteCore_write_len_zero I.calldata currentLengthZeroMem payloadStart.toNat 160)
    hawCopy
    (by evm_ov)
  have rd224 := evm_run rd220 with [push0, dup2, dup5, add]
  let awPad : UInt256 :=
    UInt256.ofNat (MachineState.M awCopy.toNat (⟨160⟩ : UInt256).toNat 32)
  have rd225 := RD.mstore
    (Cₘ awPad - Cₘ awCopy)
    currentLengthZeroReturnMem
    awPad
    rd224 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy, awPad]
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩ + ⟨0⟩).toNat) =
          (⟨160⟩ : UInt256).toNat by native_decide])
    (by rfl)
    (by
      rw [show (((⟨32⟩ : UInt256) + ⟨128⟩ + ⟨0⟩).toNat) =
          (⟨160⟩ : UInt256).toNat by native_decide])
    (by evm_ov)
  have rd1350 := evm_run rd225 with [
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, swap1, pop,
    dup1, dup4, add, swap3, pop, pop, pop, pop, pop, pop, pop, swap1, pop,
    dup1, push0, swap1, dup2, push2 ⟨261⟩, swap2, swap1, push2 ⟨1350⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [awCopy, awPad, MachineState.M] using rd1350⟩

theorem bytesStoreLiteCoreX_setEmptyWriteShortZero {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hheader : currentLengthHeaderWord σ I = ⟨0⟩) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [
    jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT (by decide) (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hdecoded := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    (mem := currentLengthZeroReturnMem) (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    (by rw [hheader]; decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hheader] using rd1394₀⟩
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1405 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  have rd1436 := evm_run rd1405 with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiNT (by decide),
    push0, dup5, iszero, push2 ⟨1436⟩, jumpiT (by decide) (by jump_dest)]
  have rd1323 := evm_run rd1436 with [
    jumpdest, push2 ⟨1446⟩, dup6, dup3, push2 ⟨1323⟩, jump (by jump_dest)]
  have rd1446 := evm_run rd1323 with [
    jumpdest, push0, push2 ⟨1334⟩, dup4, dup4, push2 ⟨1295⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨1310⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨1283⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, lor, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1448pre := evm_run rd1446 with [jumpdest, dup7]
  obtain ⟨_, _, rd1449₀⟩ := rd1448pre.sstore hperm (by native_decide) (by evm_ov)
  have hpacked0 :
      ((⟨0⟩ : UInt256).land ((⟨0⟩ : UInt256).lnot.shiftLeft ((⟨8⟩ : UInt256).mul ⟨0⟩)).lnot).lor
          ((⟨2⟩ : UInt256).mul ⟨0⟩) = ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, rd1449⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [⟨0⟩, (⟨0⟩ : UInt256).gt ⟨31⟩, ⟨32⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
          ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩,
          bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, hpacked0] using rd1449₀⟩
  exact ⟨_, _, evm_run rd1449 with [
    pop, push2 ⟨1549⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, pop, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_setEmptyWriteShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT (by decide) (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    (mem := currentLengthZeroReturnMem) (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hflag
    hvalidHeader
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1394₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1405 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiT
      (by
        rw [show UInt256.gt len ⟨31⟩ = UInt256.lt ⟨31⟩ len from rfl, hnotGt31]
        decide)
      (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  have rd1436 := evm_run rd1405 with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiNT (by decide),
    push0, dup5, iszero, push2 ⟨1436⟩, jumpiT (by decide) (by jump_dest)]
  have rd1323 := evm_run rd1436 with [
    jumpdest, push2 ⟨1446⟩, dup6, dup3, push2 ⟨1323⟩, jump (by jump_dest)]
  have rd1446 := evm_run rd1323 with [
    jumpdest, push0, push2 ⟨1334⟩, dup4, dup4, push2 ⟨1295⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨1310⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨1283⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, lor, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1448pre := evm_run rd1446 with [jumpdest, dup7]
  obtain ⟨_, _, rd1449₀⟩ := rd1448pre.sstore hperm (by native_decide) (by evm_ov)
  have hpacked0 :
      ((⟨0⟩ : UInt256).land ((⟨0⟩ : UInt256).lnot.shiftRight ((⟨8⟩ : UInt256).mul ⟨0⟩)).lnot).lor
          ((⟨2⟩ : UInt256).mul ⟨0⟩) = ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, rd1449⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
        [⟨0⟩, UInt256.gt ⟨0⟩ ⟨31⟩, ⟨32⟩, len, ⟨0⟩, ⟨0⟩,
          ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩,
          bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, hpacked0] using rd1449₀⟩
  exact ⟨_, _, evm_run rd1449 with [
    pop, push2 ⟨1549⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, pop, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_setWriteShortPackedFrom1436 {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {payloadStart len oldLen payloadWord aw : UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1436⟩
      [payloadWord, UInt256.gt len ⟨31⟩, ⟨32⟩, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (setShortPackedHeader payloadWord len)) k' C' := by
  have rd1323 := evm_run hreach with [
    jumpdest, push2 ⟨1446⟩, dup6, dup3, push2 ⟨1323⟩, jump (by jump_dest)]
  have rd1446 := evm_run rd1323 with [
    jumpdest, push0, push2 ⟨1334⟩, dup4, dup4, push2 ⟨1295⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨1310⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨1283⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, lor, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1448pre := evm_run rd1446 with [jumpdest, dup7]
  obtain ⟨_, _, rd1449₀⟩ := rd1448pre.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa only [sstoreAccountMap, initState, setShortPackedHeader] using
      (evm_run rd1449₀ with [
        pop, push2 ⟨1549⟩, jump (by jump_dest),
        jumpdest, pop, pop, pop, pop, pop, pop, jump (by jump_dest)])⟩

theorem bytesStoreLiteCoreX_setWriteShortPayloadLoadedFrom1405 {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {payloadStart len oldLen : UInt256} {k C : Nat}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1436⟩
        [setHelperPayloadWord I.calldata len payloadStart, UInt256.gt len ⟨31⟩, ⟨32⟩,
          oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperPayloadAw len)
        ByteArray.empty (cA, τ) k' C' := by
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hshort
  have hnonzero : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by rw [hzero]; rfl)
  have hlenNotZero : UInt256.isZero len = ⟨0⟩ :=
    isZero_eq_zero_of_ne hnonzero
  have rd1430 := evm_run hreach with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiNT
      (by
        rw [show UInt256.gt len ⟨31⟩ = UInt256.lt ⟨31⟩ len from rfl, hnotGt31]
        decide),
    push0, dup5, iszero, push2 ⟨1436⟩,
    jumpiNT
      (by
        rw [hlenNotZero]),
    dup3, dup8, add]
  have haddrWord : ((⟨128⟩ : UInt256) + ⟨32⟩) = ⟨160⟩ := by native_decide
  have haddr : (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) = 160 := by native_decide
  have rd1434 := RD.mload
    (Cₘ (setHelperPayloadAw len) - Cₘ (setHelperEntryAw len))
    (setHelperPayloadWord I.calldata len payloadStart)
    (setHelperPayloadAw len)
    rd1430 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        setHelperPayloadAw, haddr])
    (by simp only [setHelperPayloadWord, haddrWord])
    (by simp [setHelperPayloadAw, haddr])
    (by evm_ov)
  exact ⟨_, _, by simpa only using evm_run rd1434 with [swap1, pop]⟩

theorem bytesStoreLiteCoreX_setWriteShortNonemptyFrom1405 {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {payloadStart len oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperPayloadAw len)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len)) k' C' := by
  obtain ⟨_, _, rd1436⟩ :=
    bytesStoreLiteCoreX_setWriteShortPayloadLoadedFrom1405 (σinit := σinit) (τ := τ)
      hnz hshort hreach
  exact bytesStoreLiteCoreX_setWriteShortPackedFrom1436 (σinit := σinit) (τ := τ)
    (payloadWord := setHelperPayloadWord I.calldata len payloadStart)
    hperm rd1436

theorem bytesStoreLiteCoreX_setWriteShortNonemptyValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (holdLen :
      oldLen = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C',
      RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperPayloadAw len)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
          (setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len)) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 len (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
        decide)
      (setPaddedMem_mload128_short_nonzero I.calldata len payloadStart hnz hshort hsrc)
      (by rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]; decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          norm_num [ABI.solcMaxU64]
          omega
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    (mem := setPaddedMem I.calldata len payloadStart) (aw := setHelperEntryAw len)
    (rdata := ByteArray.empty)
    hflag
    hvalidHeader
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd1394₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotGt31 : UInt256.lt ⟨31⟩ oldLen = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1405 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiT
      (by
        rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl,
          holdNotGt31]
        decide)
      (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact bytesStoreLiteCoreX_setWriteShortNonemptyFrom1405 (σinit := σ) (τ := σ)
    hperm hnz hshort rd1405

theorem bytesStoreLiteCoreX_setEmptyWriteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart : UInt256} {k C : Nat}
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT (by decide) (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  exact bytesStoreLiteCoreX_bytesLengthDecoderLongMalformedSetMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_setEmptyWriteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart : UInt256} {k C : Nat}
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
        ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT (by decide) (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  exact bytesStoreLiteCoreX_bytesLengthDecoderShortMalformedSetMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_setShortNonemptyMalformedPanic {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {stk : List UInt256}
    (_hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨903⟩ stk
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len) ByteArray.empty
      (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd903⟩ := hreach
  have hawGe : 5 ≤ (setHelperEntryAw len).toNat :=
    setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have rd824 := evm_run rd903 with [
    push2 ⟨910⟩, push2 ⟨824⟩, jump (by jump_dest)]
  have rd825 := rd824.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd858 := rd825.pushConst solcPanicSelectorWord (width := 32)
    (op := Operation.POp.PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd858 with [
    push0,
    raw mstore 0 (setMalformedPanicMem1Of (setPaddedMem I.calldata len payloadStart))
      (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [set_mstoreCostSpec (aw := setHelperEntryAw len) (off := ⟨0⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat (MachineState.M (setHelperEntryAw len).toNat 0 32)) -
            Cₘ (setHelperEntryAw len) = 0
        rw [set_activeWordsMstore0_eq_self (aw := setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (set_activeWordsMstore0_eq_self (aw := setHelperEntryAw len) (by omega))
      (by simp only [List.length_cons]; omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 (setMalformedPanicMemOf (setPaddedMem I.calldata len payloadStart))
      (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw' hstk
        rw [set_mstoreCostSpec (aw := setHelperEntryAw len) (off := ⟨4⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat (MachineState.M (setHelperEntryAw len).toNat 4 32)) -
            Cₘ (setHelperEntryAw len) = 0
        rw [set_activeWordsMstore4_eq_self (aw := setHelperEntryAw len) (by omega)]
        simp)
      (by rfl)
      (set_activeWordsMstore4_eq_self (aw := setHelperEntryAw len) (by omega))
      (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide)
      (by
        intro s haw' hstk
        rw [set_revertCostSpec (aw := setHelperEntryAw len) (off := ⟨0⟩)
          (len := ⟨36⟩) s haw' hstk]
        change Cₘ (UInt256.ofNat (MachineState.M (setHelperEntryAw len).toNat 0 36)) -
            Cₘ (setHelperEntryAw len) = 0
        rw [set_activeWordsRevert0_36_eq_self (aw := setHelperEntryAw len) (by omega)]
        simp)
      (by simp only [List.length_cons]; omega)]

theorem bytesStoreLiteCoreX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) (setPaddedMem I.calldata len payloadStart)
      (setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd892 := rd882.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd892 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len header ret : UInt256} {rest : List UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      (header :: ret :: rest) (setPaddedMem I.calldata len payloadStart)
      (setHelperEntryAw len) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd869⟩ := hreach
  have rd882 := evm_run rd869 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨892⟩]
  have rd886 := rd882.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd903 := evm_run rd886 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨911⟩]
  have rd903' := rd903.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact bytesStoreLiteCoreX_setShortNonemptyMalformedPanic
    (payloadStart := payloadStart) (len := len) hnz hlenMax ⟨_, _, rd903'⟩
    (by simp only [List.length_cons]; omega)

theorem bytesStoreLiteCoreX_setShortNonemptyWriteLongMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len : UInt256} {k C : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 len (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        rw [set_mloadCostSpec (aw := setHelperEntryAw len) (off := ⟨128⟩) s haw hstk]
        rw [set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax)]
        simp)
      (setPaddedMem_mload128_nonzero_u64 I.calldata len payloadStart hnz hlenMax hsrc)
      (by
        exact set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax))
      (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          exact hlenMax
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  exact bytesStoreLiteCoreX_bytesLengthDecoderLongMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_setShortNonemptyWriteShortMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len : UInt256} {k C : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
        ⟨0⟩) :
    RDrev bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 len (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        rw [set_mloadCostSpec (aw := setHelperEntryAw len) (off := ⟨128⟩) s haw hstk]
        rw [set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax)]
        simp)
      (setPaddedMem_mload128_nonzero_u64 I.calldata len payloadStart hnz hlenMax hsrc)
      (by
        exact set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax))
      (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          exact hlenMax
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  exact bytesStoreLiteCoreX_bytesLengthDecoderShortMalformedShortNonemptySetMem
    (payloadStart := payloadStart) (len := len)
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I])
    hnz hlenMax hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteCoreX_setEmptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      currentLengthZeroReturnMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 0 setEmptyReturnMem (UInt256.ofNat 6) (by decide)
      mem_cost
      (by
        rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]
        rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      setEmptyReturnMem_mload64
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨160⟩ : UInt256) + ⟨32⟩) ⟨160⟩).toNat = 32 from by decide,
          setEmptyReturnMem_read160])
      (by evm_ov)]

theorem bytesStoreLiteCoreX_setShortNonemptyReturnFromWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperPayloadAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have haw : setHelperPayloadAw len = ⟨7⟩ :=
    setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 len (setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (setPaddedMem_mload128_short_nonzero_payloadAw I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (setHelperPayloadAw len) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (setPaddedMem_mload64_short_nonzero I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero
      (by
        intro hzero
        apply hnz
        rw [hzero]
        decide)
      hshort
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 0 (setShortReturnMem I.calldata len payloadStart)
      (UInt256.ofNat 7) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw, hfree]
        decide)
      (by rw [hfree, show (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) = 192 from by decide]; rfl)
      (by rw [haw, hfree]; decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (UInt256.ofNat 7) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (setShortReturnMem_mload64 I.calldata len payloadStart hnz hshort hsrc)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (by
        rw [hfree, show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨192⟩ : UInt256) + ⟨32⟩) ⟨192⟩).toNat = 32 from by decide,
          setShortReturnMem_read192 I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteCoreX_setShortEmptyValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hheader : currentLengthHeaderWord σ I = ⟨0⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k175 C175 := by
    simpa [payloadStart, hlenZero] using rd175₀
  obtain ⟨_, _, rd1350⟩ := bytesStoreLiteCoreX_setEmptyReachStorageWrite
    (payloadStart := payloadStart) rd175
  exact bytesStoreLiteCoreX_setEmptyReturnFromWrite
    (bytesStoreLiteCoreX_setEmptyWriteShortZero hperm rd1350 hheader)

theorem bytesStoreLiteCoreX_clearCurrentZeroReachCopyDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hdecoded : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨307⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      [currentLengthHeaderWord σ I, ⟨351⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd307⟩ := hdecoded
  have rd330 := evm_run rd307 with [
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
  have rd340 := evm_run rd330 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 currentLengthZeroMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd343 := evm_run rd340 with [dup1]
  obtain ⟨_, _, rd343₀⟩ := rd343.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd343'⟩ : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨343⟩
      [currentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd343₀⟩
  exact ⟨_, _, evm_run rd343' with [
    push2 ⟨351⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentZeroReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨869⟩
      [currentLengthHeaderWord σ I, ⟨351⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hdecoded := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd351₀⟩ := hdecoded
  obtain ⟨_, _, rd351⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨351⟩
        [⟨0⟩, ⟨0⟩, ⟨160⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨153⟩, bytesStoreLiteCoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd351₀⟩
  have rd357 := evm_run rd351 with [jumpdest, dup1, iszero, push2 ⟨426⟩]
  have rd426 := rd357.jumpiT (by decide) (by decide) (by jump_dest) (by evm_ov)
  have rd435 := evm_run rd426 with [
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd436 := evm_run rd435 with [
    raw mload 0 ⟨0⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      currentLengthZeroMem_mload128
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd436 with [
    swap2, pop, push0, push0, push2 ⟨449⟩, swap2, swap1, push2 ⟨453⟩,
    jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentDeleteShortZero {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [⟨0⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd453⟩ := hreach
  have rd457pre := evm_run rd453 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd457₀⟩ := rd457pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd457⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨457⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd457₀⟩
  have hdecode := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd457 with [
      push2 ⟨465⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨465⟩)
    (rest := [⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    (mem := currentLengthZeroMem) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hflag
    hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd465₀⟩ := hdecode
  obtain ⟨_, _, rd465⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨465⟩
        [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd465₀⟩
  have rd468pre := evm_run rd465 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd469₀⟩ := rd468pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd469⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨469⟩
        [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd469₀⟩
  have rd476 := evm_run rd469 with [dup1, push1 ⟨31⟩, lt, push2 ⟨483⟩]
  have rd477 := rd476.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd509 := evm_run rd477 with [pop, pop, push2 ⟨509⟩, jump (by jump_dest)]
  have rd449 := evm_run rd509 with [jumpdest, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd449 with [jumpdest, pop, swap1, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentZeroReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [⟨0⟩, bytesStoreLiteCoreSelWord I]
      currentLengthZeroMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd153⟩ := hreach
  have rd744 := evm_run rd153 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      currentLengthZeroMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨166⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 3 currentLengthZeroReturnMem (UInt256.ofNat 6) (by decide)
      mem_cost
      (by rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd166 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd166 with [
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

theorem bytesStoreLiteCoreX_clearCurrentShortZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ = ⟨0⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray ⟨0⟩) := by
  have hdecoded₀ := bytesStoreLiteCoreX_bytesLengthDecoderShortValid
    (hreach := bytesStoreLiteCoreX_clearCurrentReachDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨307⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    hflag
    hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd307₀⟩ := hdecoded₀
  have hdecoded : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨307⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hzero] using rd307₀⟩
  have hcopy := bytesStoreLiteCoreX_clearCurrentZeroReachCopyDecoder hdecoded
  have hdelStart := bytesStoreLiteCoreX_clearCurrentZeroReachDelete hcopy
    hflag hvalid hzero
  exact bytesStoreLiteCoreX_clearCurrentZeroReturnFromWrapper
    (bytesStoreLiteCoreX_clearCurrentDeleteShortZero hperm hdelStart hflag hvalid hzero)

theorem bytesStoreLiteCoreX_clearCurrentShortReachDelete {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      (currentLengthPayloadMem len (currentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded₀ := bytesStoreLiteCoreX_bytesLengthDecoderShortValid
    (hreach := bytesStoreLiteCoreX_clearCurrentReachDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨307⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd307₀⟩ := hdecoded₀
  obtain ⟨_, _, rd307⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨307⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd307₀⟩
  have rd330 := evm_run rd307 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd340 := evm_run rd330 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd343 := evm_run rd340 with [dup1]
  obtain ⟨_, _, rd343₀⟩ := rd343.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd343'⟩ : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨343⟩
      [currentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd343₀⟩
  have hdecode := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd343' with [
      push2 ⟨351⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨351⟩)
    (rest := [⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
      bytesStoreLiteCoreSelWord I])
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd351₀⟩ := hdecode
  obtain ⟨_, _, rd351⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨351⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd351₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotZero : UInt256.isZero len = ⟨0⟩ := isZero_eq_zero_of_ne hnonzero
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd357 := evm_run rd351 with [jumpdest, dup1, iszero, push2 ⟨426⟩]
  have rd358 := rd357.jumpiNT (by decide) hnotZero (by evm_ov)
  have rd385 := evm_run rd358 with [dup1, push1 ⟨31⟩, lt, push2 ⟨385⟩]
  have rd366 := rd385.jumpiNT (by native_decide) hnotGt31 (by evm_ov)
  have rd371pre := evm_run rd366 with [push2 ⟨256⟩, dup1, dup4]
  obtain ⟨_, _, rd372₀⟩ := rd371pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd372⟩ : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨372⟩
      [currentLengthHeaderWord σ I, ⟨256⟩, ⟨256⟩, len, ⟨0⟩, ⟨160⟩, len,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd372₀⟩
  have rd376 := evm_run rd372 with [
    div, mul, dup4,
    raw mstore 3 (currentLengthPayloadMem len (currentLengthHeaderWord σ I))
      (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have rd426 := evm_run rd376 with [
    swap2, push1 ⟨32⟩, add, swap2, push2 ⟨426⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1,
    raw mload 0 len (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (currentLengthPayloadMem_mload128 len (currentLengthHeaderWord σ I))
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [hfree] using
      (evm_run rd426 with [
        swap2, pop, push0, push0, push2 ⟨449⟩, swap2, swap1, push2 ⟨453⟩,
        jump (by jump_dest)])⟩

theorem bytesStoreLiteCoreX_clearCurrentDeleteShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [len, bytesStoreLiteCoreSelWord I]
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd453⟩ := hreach
  have rd457pre := evm_run rd453 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd457₀⟩ := rd457pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd457⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨457⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd457₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecode := bytesStoreLiteCoreX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd457 with [
      push2 ⟨465⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨465⟩)
    (rest := [⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    (mem := mem) (aw := aw) (rdata := rdata)
    hflag hvalidHeader
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd465₀⟩ := hdecode
  obtain ⟨_, _, rd465⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨465⟩
        [len, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd465₀⟩
  have rd468pre := evm_run rd465 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd469₀⟩ := rd468pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd469⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨469⟩
        [len, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd469₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd476 := evm_run rd469 with [dup1, push1 ⟨31⟩, lt, push2 ⟨483⟩]
  have rd477 := rd476.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd509 := evm_run rd477 with [pop, pop, push2 ⟨509⟩, jump (by jump_dest)]
  have rd449 := evm_run rd509 with [jumpdest, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd449 with [jumpdest, pop, swap1, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentShortReturnFromWrapper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [len, bytesStoreLiteCoreSelWord I]
      (currentLengthPayloadMem len (currentLengthHeaderWord σ I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C)
    (hfree : currentLengthFreePtr len = ⟨192⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd153⟩ := hreach
  have rd744 := evm_run rd153 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (currentLengthPayloadMem_mload64 len (currentLengthHeaderWord σ I) ⟨192⟩ hfree)
      (by decide) (by evm_ov),
    push2 ⟨166⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 3 (currentLengthPayloadReturnMem len (currentLengthHeaderWord σ I))
      (UInt256.ofNat 7) (by decide)
      mem_cost
      (by rw [show (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) = 192 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd166 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd166 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 7) (by decide)
      mem_cost
      (currentLengthPayloadReturnMem_mload64 len (currentLengthHeaderWord σ I)
        ⟨192⟩ hfree)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by decide)
      mem_cost
      (by
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨192⟩ : UInt256) + ⟨32⟩) ⟨192⟩).toNat = 32 from by decide,
          currentLengthPayloadReturnMem_read192])
      (by evm_ov)]

theorem bytesStoreLiteCoreX_clearCurrentShortValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    RDret bytesStoreLiteCoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (UInt256.toByteArray len) := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hnonzero hlt32
  have hdelStart := bytesStoreLiteCoreX_clearCurrentShortReachDelete
    (g := g) hreach hflag hlen hvalid hnonzero
  have hdel := bytesStoreLiteCoreX_clearCurrentDeleteShortValid
    (g := g) hperm hdelStart hflag hlen hvalid
  exact bytesStoreLiteCoreX_clearCurrentShortReturnFromWrapper hdel hfree

theorem clearCurrent_len_toNat_lt_sign_of_div2 {header len : UInt256}
    (hlen : len = UInt256.div header ⟨2⟩) :
    len.toNat < 2 ^ 255 := by
  have hlenNat : len.toNat = header.toNat / 2 := by
    rw [hlen, udiv_toNat]
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [hlenNat]
  apply Nat.div_lt_of_lt_mul
  have hheader : header.toNat < UInt256.size := header.val.isLt
  norm_num [UInt256.size] at hheader ⊢
  exact hheader

theorem clearCurrent_land_one_eq_one_of_ne_zero {w : UInt256}
    (h : UInt256.land w ⟨1⟩ ≠ ⟨0⟩) :
    UInt256.land w ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  change (UInt256.land w ⟨1⟩).toNat = 1
  have hbit := uInt256_land_one_toNat w
  have hlt : (UInt256.land w ⟨1⟩).toNat < 2 := by
    rw [hbit]
    exact Nat.mod_lt _ (by decide)
  have hne : (UInt256.land w ⟨1⟩).toNat ≠ 0 := by
    intro hz
    exact h (uint256_toNat_eq_zero hz)
  omega

theorem clearCurrent_ult_eq_one_of_ne_zero {a b : UInt256}
    (h : UInt256.lt a b ≠ ⟨0⟩) :
    UInt256.lt a b = ⟨1⟩ := by
  have hlt := ult_ne_zero_toNat_lt h
  exact ult_one hlt

theorem clearCurrentLongValid_gt31 {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
  have hland : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    clearCurrent_land_one_eq_one_of_ne_zero hflag
  have hnotLt32 : UInt256.lt len ⟨32⟩ = ⟨0⟩ := by
    by_contra hltNotZero
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      clearCurrent_ult_eq_one_of_ne_zero hltNotZero
    exact hvalid (by simp [hland, hltOne, UInt256.sub])
  have hge32 : 32 ≤ len.toNat := by
    by_contra hlt
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
          Nat.lt_of_not_ge hlt)
    rw [hltOne] at hnotLt32
    contradiction
  rw [show UInt256.lt ⟨31⟩ len = ⟨1⟩ from
    ult_one (by
      rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      omega)]
  decide

noncomputable def clearCurrentBaseMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def clearCurrentBaseMemFrom (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 mem 0 32

def clearCurrentBaseAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat 0 32)

def clearCurrentHashAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (clearCurrentBaseAw aw).toNat (⟨0⟩ : UInt256).toNat
      (⟨32⟩ : UInt256).toNat)

noncomputable def clearCurrentBaseWord : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (clearCurrentBaseMem.readWithPadding 0 32)))

theorem clearCurrentBaseMem_read0 :
    clearCurrentBaseMem.readWithPadding 0 32 = UInt256.toByteArray ⟨0⟩ := by
  exact wordAt0Mem_read0 ⟨0⟩ solcFreePtrMem

theorem clearCurrentBaseWord_eq_solidityBytesDataBaseSlot :
    clearCurrentBaseWord = solidityBytesDataBaseSlot ⟨0⟩ := by
  rw [clearCurrentBaseWord, solidityBytesDataBaseSlot, clearCurrentBaseMem_read0,
    uInt256OfByteArray_eq]

theorem storageLocStore_currentPackedByte_absent_same
    {evm : EVM.State} {off : Fin 32} {byte : UInt8}
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    storageLocStore evm (uint8Loc ⟨0⟩ off) (.int byte.toNat) = some evm := by
  unfold storageLocStore
  simp [uint8Loc, storageLocWriteWord, valueToWord,
    storageStore_absent evm evm.executionEnv.codeOwner, hmissing]

theorem solidityBytesHeaderWord_long_flag {len : Nat}
    (hlong : ¬ len < 32) (hlenMax : len ≤ ABI.solcMaxU64) :
    UInt256.land (solidityBytesHeaderWord len) ⟨1⟩ ≠ ⟨0⟩ := by
  have hwordLt : len * 2 + 1 < UInt256.size := by
    have hmax : ABI.solcMaxU64 * 2 + 1 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  have hmod : (solidityBytesHeaderWord len).toNat % 2 = 1 := by
    have htoNat : (UInt256.ofNat (len * 2 + 1)).toNat = len * 2 + 1 := by
      exact ulit_toNat' (len * 2 + 1) hwordLt
    rw [solidityBytesHeaderWord, if_neg hlong, htoNat]
    omega
  intro hzero
  have hbit := uInt256_land_one_toNat (solidityBytesHeaderWord len)
  rw [hmod] at hbit
  have hzeroNat := congrArg UInt256.toNat hzero
  simp [hbit] at hzeroNat

theorem clearCurrentBaseMemFrom_read0 (mem : ByteArray) :
    (clearCurrentBaseMemFrom mem).readWithPadding 0 32 = UInt256.toByteArray ⟨0⟩ := by
  exact wordAt0Mem_read0 ⟨0⟩ mem

theorem clearCurrentBaseMemFrom_keccak (mem : ByteArray) :
    UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC ((clearCurrentBaseMemFrom mem).readWithPadding 0 32))) =
        clearCurrentBaseWord := by
  rw [clearCurrentBaseWord, clearCurrentBaseMemFrom_read0, clearCurrentBaseMem_read0]

def clearDataWordsLoopIndex (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx n

theorem clearDataWordsLoopIndex_zero_ofNat :
    ∀ i, clearDataWordsLoopIndex ⟨0⟩ i = UInt256.ofNat i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_zero_ofNat i,
        u256_one_add_ofNat]

theorem clearDataWordsLoopIndex_succ_base (idx : UInt256) :
    ∀ i, clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i =
      (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base idx i]

theorem bytesStoreLiteCoreX_clearDataWordsLoopDone {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨513⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hdone : UInt256.gt count idx = ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd511⟩ := hreach
  have hcond : UInt256.isZero (UInt256.gt count idx) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenCount : (count :: base :: ret :: rest).length = rest.length + 3 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have rd513 := rd511.jumpdest (by native_decide) hovStack
  have rd514 := rd513.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd515 := rd514.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd516 := rd515.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd517 := rd516.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd520 := rd517.push2 ⟨535⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd535 := rd520.jumpiT (by native_decide) hcond (by jump_dest)
    (by rw [hlenIdx]; omega)
  have rd536 := rd535.jumpdest (by native_decide) hovStack
  have rd537 := rd536.pop (by native_decide)
    (by rw [hlenCount]; omega)
  have rd538 := rd537.pop (by native_decide)
    (by rw [hlenBase]; omega)
  have rd539 := rd538.pop (by native_decide)
    (by rw [hlenRet]; omega)
  exact ⟨_, _, rd539.jump (by native_decide) hret (by omega)⟩

theorem bytesStoreLiteCoreX_clearDataWordsLoopStep {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨513⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.gt count idx) = ⟨0⟩)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨513⟩
      (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner τ (idx + base) ⟨0⟩) k C := by
  obtain ⟨_, _, rd511⟩ := hreach
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have rd513 := rd511.jumpdest (by native_decide) hovStack
  have rd514 := rd513.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd515 := rd514.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd516 := rd515.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd517 := rd516.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd520 := rd517.push2 ⟨535⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd522 := rd520.jumpiNT (by native_decide) hcontinue
    (by rw [hlenIdx]; omega)
  have rd523 := rd522.dup3 (by native_decide)
    (by rw [hlenRet]; omega)
  have rd524 := rd523.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd525 := rd524.add (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd526 := rd525.push0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd527 := rd526.swap1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd528⟩ := rd527.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd530 := rd528.push1 ⟨1⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd531 := rd530.add (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd534 := rd531.push2 ⟨513⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd534.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩

theorem bytesStoreLiteCoreX_clearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨513⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex idx i)) = ⟨0⟩)
    (hdone : UInt256.gt count (clearDataWordsLoopIndex idx fuel) = ⟨0⟩)
    (hret : (D_J bytesStoreLiteCoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        bytesStoreLiteCoreX_clearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
          (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret hov
  | succ n ih =>
      have hstep := bytesStoreLiteCoreX_clearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
        (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by simpa [clearDataWordsLoopIndex] using hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hstep' :
          ∃ k C, RD bytesStoreLiteCoreBytecode I g
            (initState cA gh bl σinit σ₀ g A I) ⟨513⟩
            (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
            (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
        simpa [u256_add_comm idx base] using hstep
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.gt count (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i)) =
              ⟨0⟩ := by
        intro i hi
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.gt count (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n) = ⟨0⟩ := by
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep' hcontinueTail hdoneTail

theorem bytesStoreLiteCoreX_clearCurrentDeleteLongValidToLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨513⟩
      [⟨0⟩, UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩, clearCurrentBaseWord,
        ⟨508⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      (clearCurrentBaseMemFrom mem) (clearCurrentHashAw aw) rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd453⟩ := hreach
  have rd457pre := evm_run rd453 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd457₀⟩ := rd457pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd457⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨457⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩,
          bytesStoreLiteCoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd457₀⟩
  have hdecode := bytesStoreLiteCoreX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd457 with [
      push2 ⟨465⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨465⟩)
    (rest := [⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    (mem := mem) (aw := aw) (rdata := rdata)
    hflag hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd465₀⟩ := hdecode
  obtain ⟨_, _, rd465⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨465⟩
        [len, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd465₀⟩
  have rd468pre := evm_run rd465 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd469₀⟩ := rd468pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd469⟩ :
      ∃ k C, RD bytesStoreLiteCoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨469⟩
        [len, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd469₀⟩
  have rd476 := evm_run rd469 with [dup1, push1 ⟨31⟩, lt, push2 ⟨483⟩]
  have rd483 := rd476.jumpiT (by native_decide) hgt31 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd493 := evm_run rd483 with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore (Cₘ (clearCurrentBaseAw aw) - Cₘ aw)
      (clearCurrentBaseMemFrom mem) (clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd498 := evm_run rd493 with [
    raw keccak256 (Cₘ (clearCurrentHashAw aw) - Cₘ (clearCurrentBaseAw aw))
      clearCurrentBaseWord (clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          clearCurrentHashAw, clearCurrentBaseAw])
      (clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov)]
  exact ⟨_, _, evm_run rd498 with [
    swap1, push2 ⟨508⟩, swap2, swap1, push2 ⟨511⟩, jump (by jump_dest),
    jumpdest, push0]⟩

theorem bytesStoreLiteCoreX_clearCurrentLoopReturnToWrapper {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {mem rdata : ByteArray} {aw len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨508⟩
      [⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨153⟩
      [len, bytesStoreLiteCoreSelWord I] mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd508⟩ := hreach
  have rd449 := evm_run rd508 with [jumpdest, jumpdest, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd449 with [jumpdest, pop, swap1, jump (by jump_dest)]⟩

theorem bytesStoreLiteCoreX_clearCurrentDeleteLongValidWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [len, bytesStoreLiteCoreSelWord I]
      (clearCurrentBaseMemFrom mem) (clearCurrentHashAw aw) rdata
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩ fuel) k C := by
  have hloopStart := bytesStoreLiteCoreX_clearCurrentDeleteLongValidToLoop
    (g := g) hperm hreach hflag hvalid hlen hgt31
  have hloop := bytesStoreLiteCoreX_clearDataWordsLoopGenerated
    (σinit := σ) (τ := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
    (base := clearCurrentBaseWord)
    (ret := (⟨508⟩ : UInt256))
    (rest := [⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I])
    (mem := clearCurrentBaseMemFrom mem) (aw := clearCurrentHashAw aw)
    (rdata := rdata)
    (fuel := fuel)
    hperm hloopStart hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteCoreX_clearCurrentLoopReturnToWrapper hloop

theorem bytesStoreLiteCoreX_clearCurrentDeleteLongValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, bytesStoreLiteCoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteCoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨153⟩
      [len, bytesStoreLiteCoreSelWord I]
      (clearCurrentBaseMemFrom mem) (clearCurrentHashAw aw) rdata
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat) k C := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteCoreX_clearCurrentDeleteLongValidWithLoopSchedule
      (g := g) (len := len) (fuel := count.toNat)
      hperm hreach hflag hvalid hlen hgt31 hcontinue hdone

/-! ## `currentLength()` runtime equivalence -/

theorem bytesStoreLiteCoreCurrentLengthLongMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨115⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_currentLength (I := I) hsz
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
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hbad]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact currentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteCoreX_currentLengthLongMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreCurrentLengthShortMalformedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨115⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_currentLength (I := I) hsz
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
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hbad0]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body .reverted := by
    exact currentLengthBodyRevertsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteCoreX_currentLengthShortMalformed
      (g := Sat256.ofUInt256 g) hreach hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreCurrentLengthLongValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨115⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_currentLength (I := I) hsz
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
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hvalid]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreLiteCoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat)))) := by
    exact currentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteCoreX_currentLengthLongValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)))

theorem bytesStoreLiteCoreCurrentLengthShortValidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨115⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_currentLength (I := I) hsz
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
  have hlen :
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hvalid0]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := bytesStoreLiteCoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int
            (Int.ofNat
              (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)))) := by
    exact currentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteCoreX_currentLengthShortValid
      (g := Sat256.ofUInt256 g) hreach hflag hvalid)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode
        (uint256ReturnEncoding
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)))

theorem bytesStoreLiteCoreCurrentLengthBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨115⟩
      [bytesStoreLiteCoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteCoreCurrentLengthShortValidBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteCoreCurrentLengthShortMalformedBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteCoreCurrentLengthLongValidBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreLiteCoreCurrentLengthLongMalformedBodyCore hcode hsize hperm hwv hsel hreach
        hAccounts hflag hbad

theorem bytesStoreLiteCoreCurrentLengthRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact bytesStoreLiteCoreCurrentLengthBodyCore hcode hsize hperm hwv hsel
    (bytesStoreLiteCoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts

theorem bytesStoreLiteCoreClearCurrentLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteCoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hrev := bytesStoreLiteCoreX_clearCurrentLongMalformed hreach hflag hbad
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
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hbad]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact clearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreClearCurrentShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteCoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hrev := bytesStoreLiteCoreX_clearCurrentShortMalformed hreach hflag hbad
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
      readStorageBytesLength? bytesStoreLiteCoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, bytesStoreLiteCoreLayout,
      initState, hload', hflag, hbad0]
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact clearCurrentBodyRevertsOfRead
      (by simp only [initState]; exact hwv) hlen
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreClearCurrentShortZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hheader : currentLengthHeaderWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteCoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    decide
  have hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hheader]
    decide
  have hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ =
      ⟨0⟩ := by
    rw [hheader]
    decide
  have hret := bytesStoreLiteCoreX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hvalid hzero
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hload' :
        Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hheader] using hload'
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    simpa [evmSolm0, initState] using hload
  have hlen :
      readStorageBytesLength? bytesStoreLiteCoreConfig evmSolm0 { base := "current" } = .ok 0 := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteCoreConfig, bytesStoreLiteCoreStorageLayout, solidityStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader_zero, bytesStoreLiteCoreLayout,
      hloadBytes]
  have hread :
      evalExpr? bytesStoreLiteCoreConfig { contract := bytesStoreLiteCoreContract, locals := ∅ }
        evmSolm0 (.storage currentRef) = .ok (.bytes ByteArray.empty) := by
    rw [evalExpr?, currentLengthResolve]
    set_option linter.unusedSimpArgs false in
    simp [readStorage?, bytesStoreLiteCoreConfig,
      bytesStoreLiteCoreStorageLayout, solidityStorageLayout, solidityReadValue?,
      solidityReadBytesValue?, solidityBytesBaseSlotAndLength?, storageValueResultToEval,
      bytesStoreLiteCoreLayout, hloadBytes, solidityDecodeBytesLengthHeader_zero,
      EvalResult.bind, bind, pure]
  have hdel :
      deleteStorage? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using deleteCurrentShortZero (evm := evmSolm0) hload
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreLiteCoreContract,
            locals := (∅ : Store).insert "copy" (.bytes ByteArray.empty) }
          evmSolm1 (some (.int 0))) := by
    exact clearCurrentBodyReturnsZero (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hread hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreLiteCoreClearCurrentShortDecodedZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ =
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteCoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hret := bytesStoreLiteCoreX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hvalid hzero
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  have hvalidLen :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hzero] using hvalid
  obtain ⟨copy, hread, hcopySize⟩ :=
    readCurrentShortPackedExists (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := ⟨0⟩)
      hloadBytes hflag hzero.symm hvalidLen
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hdel :
      deleteStorage? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      deleteCurrentShortPacked (evm := evmSolm0)
        (header := currentLengthHeaderWord σ_evm I) (len := ⟨0⟩) (copy := copy)
        hloadBytes hpacked hflag hzero.symm hvalidLen
  have hbodyBytes := clearCurrentBodyReturnsBytes (evm := evmSolm0) (evm' := evmSolm1)
    (copy := copy) (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreLiteCoreContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int 0))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreLiteCoreClearCurrentShortNonzeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen : len =
      UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hnonzero : len ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := bytesStoreLiteCoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := bytesStoreLiteCoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreLiteCoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hret := bytesStoreLiteCoreX_clearCurrentShortValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hlen hvalid hnonzero
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  obtain ⟨copy, hread, hcopySize⟩ :=
    readCurrentShortPackedExists (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := len)
      hloadBytes hflag hlen hvalid
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hdel :
      deleteStorage? bytesStoreLiteCoreConfig
        { contract := bytesStoreLiteCoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      deleteCurrentShortPacked (evm := evmSolm0)
        (header := currentLengthHeaderWord σ_evm I) (len := len) (copy := copy)
        hloadBytes hpacked hflag hlen hvalid
  have hbodyBytes := clearCurrentBodyReturnsBytes (evm := evmSolm0) (evm' := evmSolm1)
    (copy := copy) (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreLiteCoreContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int len.toNat))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode (uint256ReturnEncoding len))

theorem bytesStoreLiteCoreSetShortEmptyRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hheader : currentLengthHeaderWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hret := bytesStoreLiteCoreX_setShortEmptyValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord
    hsizeSign hlenZero hheader
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hload' :
        Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hheader] using hload'
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    simpa [evmSolm0, initState] using hload
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      writeCurrentEmptyFromZero (evm := evmSolm0) hloadBytes
  exact setRuntimeOfWriteAccountMapEquiv hcode hwv hret hd hdec hwrite
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreLiteCoreSetEmptyShortValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  let len : UInt256 :=
    UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [payloadStart, hlenZero] using rd175₀
  obtain ⟨_, _, rd1350⟩ := bytesStoreLiteCoreX_setEmptyReachStorageWrite
    (payloadStart := payloadStart) rd175
  have hret := bytesStoreLiteCoreX_setEmptyReturnFromWrite
    (payloadStart := payloadStart)
    (bytesStoreLiteCoreX_setEmptyWriteShortValid
      (payloadStart := payloadStart) (len := len) hperm rd1350 hflag rfl
      (by simpa [len] using hvalid))
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .ok evmSolm1 := by
    have hwrite₀ := writeCurrentShortPacked (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := len) (value := ByteArray.empty)
      (by decide) hloadBytes hpacked hflag rfl (by simpa [len] using hvalid)
    simpa [evmSolm1, hshortEmpty] using hwrite₀
  exact setRuntimeOfWriteAccountMapEquiv hcode hwv hret hd hdec hwrite
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreLiteCoreSetEmptyLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [payloadStart, hlenZero] using rd175₀
  obtain ⟨_, _, rd1350⟩ := bytesStoreLiteCoreX_setEmptyReachStorageWrite
    (payloadStart := payloadStart) rd175
  have hrev := bytesStoreLiteCoreX_setEmptyWriteLongMalformed
    (payloadStart := payloadStart) rd1350 hflag hbad
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert :=
    writeCurrentMalformedLong (evm := evmSolm0) (header := currentLengthHeaderWord σ_evm I)
      (value := ByteArray.empty) hload hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) setTransition.body .reverted :=
    setBodyRevertsOfWrite (evm := evmSolm0) (value := ByteArray.empty)
      (by simp [evmSolm0, initState]; exact hwv) hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreSetEmptyShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
        ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [payloadStart, hlenZero] using rd175₀
  obtain ⟨_, _, rd1350⟩ := bytesStoreLiteCoreX_setEmptyReachStorageWrite
    (payloadStart := payloadStart) rd175
  have hrev := bytesStoreLiteCoreX_setEmptyWriteShortMalformed
    (payloadStart := payloadStart) rd1350 hflag hbad
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes ByteArray.empty) = .revert :=
    writeCurrentMalformedShort (evm := evmSolm0) (header := currentLengthHeaderWord σ_evm I)
      (value := ByteArray.empty) hload hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) setTransition.body .reverted :=
    setBodyRevertsOfWrite (evm := evmSolm0) (value := ByteArray.empty)
      (by simp [evmSolm0, initState]; exact hwv) hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreSetShortNonemptyLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_some (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  have hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
  have hshort : len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewShort
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hnz : len.toNat ≠ 0 := by
    intro hz
    apply hnonzero
    apply u256_inj
    simpa [len] using hz
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart]
    rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
    have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero_of_payload I.calldata hsize hoffMax hlenWord hlenMax hpayload
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    bytesStoreLiteCoreX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hrev := bytesStoreLiteCoreX_setShortNonemptyWriteLongMalformed
    (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbad
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes (setDecodedValueBytes I)) = .revert :=
    writeCurrentMalformedLong (evm := evmSolm0) (header := currentLengthHeaderWord σ_evm I)
      (value := setDecodedValueBytes I) hload hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes (setDecodedValueBytes I))) setTransition.body
        .reverted :=
    setBodyRevertsOfWrite (evm := evmSolm0) (value := setDecodedValueBytes I)
      (by simp [evmSolm0, initState]; exact hwv) hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreSetShortNonemptyShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_some (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  have hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
  have hshort : len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewShort
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hnz : len.toNat ≠ 0 := by
    intro hz
    apply hnonzero
    apply u256_inj
    simpa [len] using hz
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart]
    rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
    have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero_of_payload I.calldata hsize hoffMax hlenWord hlenMax hpayload
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    bytesStoreLiteCoreX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hrev := bytesStoreLiteCoreX_setShortNonemptyWriteShortMalformed
    (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbad
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes (setDecodedValueBytes I)) = .revert :=
    writeCurrentMalformedShort (evm := evmSolm0) (header := currentLengthHeaderWord σ_evm I)
      (value := setDecodedValueBytes I) hload hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteCoreConfig bytesStoreLiteCoreContract evmSolm0
        ((∅ : Store).insert "value" (.bytes (setDecodedValueBytes I))) setTransition.body
        .reverted :=
    setBodyRevertsOfWrite (evm := evmSolm0) (value := setDecodedValueBytes I)
      (by simp [evmSolm0, initState]; exact hwv) hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteCoreSetHeadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_headShort (I := I) hsz hshort
  have hrev := bytesStoreLiteCoreX_setDecoderHeadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem bytesStoreLiteCoreSetHeadHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_huge (I := I) hbig
  have hrev := bytesStoreLiteCoreX_setDecoderHeadHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hbig
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem bytesStoreLiteCoreSetOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_offsetHuge (I := I) hsz36 hoff
  have hrev := bytesStoreLiteCoreX_setDecoderOffsetHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoff
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem bytesStoreLiteCoreSetLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_lengthShort (I := I) hsz36 hhi hshort
  have hrev := bytesStoreLiteCoreX_setDecoderLengthShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem bytesStoreLiteCoreSetLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_lengthHuge (I := I)
    hsz36 hhi hoffMax hlenWord hlenHuge
  have hrev := bytesStoreLiteCoreX_setDecoderLengthHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    (setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
    (setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge)
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem bytesStoreLiteCoreSetPayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_payloadShort (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  have hrev := bytesStoreLiteCoreX_setDecoderPayloadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    (setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
    (setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
    hpayloadWord
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

end BytesStoreLiteCore
