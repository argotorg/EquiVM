import Benchmarks.CompoundIII.CometRewards.Trusted
import Benchmarks.CompoundIII.CometRewards.Spec
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# CometRewards shared proof scaffold

This file records the bytecode dispatch order and the exact body-entry stack shapes produced by
the via-IR dispatcher.  The prefix is not the standard `solcDispatchReachBody` prefix, so the
`cometRewardsReach...` lemmas are local proof obligations rather than uses of the generic driver.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev cometRewardsSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

theorem selectorFalseOfMatch {I : ExecutionEnv} {want other : ByteArray}
    (hne : other ≠ want) (hsel : selIs I want) :
    (other == I.calldata.extract 0 4) = false := by
  by_cases hother : (other == I.calldata.extract 0 4) = true
  · have hotherEq : other = I.calldata.extract 0 4 := by
      apply ByteArray.ext
      rw [show (other == I.calldata.extract 0 4) =
        (other.data == (I.calldata.extract 0 4).data) from rfl] at hother
      exact beq_iff_eq.mp hother
    have hwantEq : want = I.calldata.extract 0 4 := by
      apply ByteArray.ext
      change (want == I.calldata.extract 0 4) = true at hsel
      rw [show (want == I.calldata.extract 0 4) =
        (want.data == (I.calldata.extract 0 4).data) from rfl] at hsel
      exact beq_iff_eq.mp hsel
    exact False.elim (hne (by rw [hotherEq, hwantEq]))
  · cases h : other == I.calldata.extract 0 4 <;> simp_all

/-! ## ABI decode helpers not yet in `Reasoning.ABI` -/

-- LIBRARY CANDIDATE: generalizes `Reasoning.Theory.decodeScalarWords_address_address_uint256_ok`
-- by replacing the third scalar word with a canonical bool.
theorem decodeScalarWords_address_address_bool_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hbool64 :
      ABI.bytesToWord ((bytes.drop 64).take 32) = ⟨0⟩ ∨
        ABI.bytesToWord ((bytes.drop 64).take 32) = ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .address, .elem .bool] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord ((bytes.drop 64).take 32))] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rcases hbool64 with hzero | hone
  · rw [decodeScalarWord_bool_ok_zero (start := 64) hlen64 hzero]
    simp [wordToElem, hzero]
  · rw [decodeScalarWord_bool_ok_one (start := 64) hlen64 hone]
    simp [wordToElem, hone]

-- LIBRARY CANDIDATE: address,address,bool scalar-list noncanonical first address branch.
theorem decodeScalarWords_address_address_bool_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: address,address,bool scalar-list noncanonical second address branch.
theorem decodeScalarWords_address_address_bool_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

-- LIBRARY CANDIDATE: address,address,bool scalar-list noncanonical bool branch.
theorem decodeScalarWords_address_address_bool_none_noncanon2 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hnz64 : ABI.bytesToWord ((bytes.drop 64).take 32) ≠ ⟨0⟩)
    (hno64 : ABI.bytesToWord ((bytes.drop 64).take 32) ≠ ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_bool_none_noncanon (start := 64) hlen64 hnz64 hno64]

-- LIBRARY CANDIDATE: address,address,bool scalar-list short calldata branch.
theorem decodeScalarWords_address_address_bool_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [.elem .address, .elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · by_cases hcanon32 :
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
          rw [decodeScalarWord_bool_none_short (start := 64) htake64n]
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: ABI calldata decoding for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus)
    (hbool : calldataWord cd 68 = ⟨0⟩ ∨ calldataWord cd 68 = ⟨1⟩) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (wordToElem .bool (calldataWord cd 68))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_bool_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)
    (by
      rcases hbool with hzero | hone
      · left
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
          calldataWord cd 68 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
        exact hzero
      · right
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
          calldataWord cd 68 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
        exact hone)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32))] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (wordToElem .bool (calldataWord cd 68)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68]

-- LIBRARY CANDIDATE: ABI calldata noncanonical first address branch for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_bool_none_noncanon0 (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc0)]

-- LIBRARY CANDIDATE: ABI calldata noncanonical second address branch for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_none_noncanon1 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_bool_none_noncanon1 (bytes := cd.toList.drop 4)
    htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hnc1)]

-- LIBRARY CANDIDATE: ABI calldata noncanonical bool branch for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_none_noncanon2 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus)
    (hnz2 : calldataWord cd 68 ≠ ⟨0⟩) (hno2 : calldataWord cd 68 ≠ ⟨1⟩) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_bool_none_noncanon2 (bytes := cd.toList.drop 4)
    htake4 htake36' htake68'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
        calldataWord cd 68 from by
          simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
      exact hnz2)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
        calldataWord cd 68 from by
          simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
      exact hno2)]

-- LIBRARY CANDIDATE: ABI calldata short branch for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_bool_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

-- LIBRARY CANDIDATE: ABI calldata huge branch for `(address,address,bool)`.
theorem decodeCalldata_address_address_bool_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

/-! ## Dispatch order and body PCs -/

/-- Function selectors in bytecode dispatch-arm order. -/
def cometRewardsSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x01, 0xe3, 0x36, 0x67]⟩  -- withdrawToken(address,address,uint256)
  | 1 => ⟨#[0x0c, 0x34, 0x0a, 0x24]⟩  -- governor()
  | 2 => ⟨#[0x22, 0x89, 0xb6, 0xb8]⟩  -- rewardConfig(address)
  | 3 => ⟨#[0x41, 0xe0, 0xca, 0xd6]⟩  -- getRewardOwed(address,address)
  | 4 => ⟨#[0x4f, 0xf8, 0x5d, 0x94]⟩  -- claimTo(address,address,address,bool)
  | 5 => ⟨#[0x63, 0x94, 0xf1, 0x61]⟩  -- setRewardsClaimed(address,address[],uint256[])
  | 6 => ⟨#[0x65, 0xe1, 0x23, 0x92]⟩  -- rewardsClaimed(address,address)
  | 7 => ⟨#[0x95, 0xe3, 0x6d, 0x2c]⟩  -- setRewardConfig(address,address)
  | 8 => ⟨#[0xb7, 0x03, 0x4f, 0x7e]⟩  -- claim(address,address,bool)
  | 9 => ⟨#[0xb8, 0xcc, 0x9c, 0xe6]⟩  -- transferGovernor(address)
  | _ => ⟨#[0xcd, 0xc0, 0xca, 0x09]⟩  -- setRewardConfigWithMultiplier(...)

theorem cometRewardsSelectorEq0 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 0 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x01 0xe3 0x36 0x67
      (⟨0x01e33667⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq1 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 1 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x0c 0x34 0x0a 0x24
      (⟨0x0c340a24⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq2 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 2 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x22 0x89 0xb6 0xb8
      (⟨0x2289b6b8⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq3 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 3 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x41 0xe0 0xca 0xd6
      (⟨0x41e0cad6⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq4 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 4 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x4f 0xf8 0x5d 0x94
      (⟨0x4ff85d94⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq5 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 5 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x63 0x94 0xf1 0x61
      (⟨0x6394f161⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq6 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 6 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x65 0xe1 0x23 0x92
      (⟨0x65e12392⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq7 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0x95e36d2c⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 7 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0x95 0xe3 0x6d 0x2c
      (⟨0x95e36d2c⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq8 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0xb7034f7e⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 8 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0xb7 0x03 0x4f 0x7e
      (⟨0xb7034f7e⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq9 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0xb8cc9ce6⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 9 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0xb8 0xcc 0x9c 0xe6
      (⟨0xb8cc9ce6⟩ : UInt256) (by native_decide))

theorem cometRewardsSelectorEq10 (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (⟨0xcdc0ca09⟩ : UInt256) (cometRewardsSelWord I) =
      if cometRewardsSelBytes 10 == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩ := by
  simpa [cometRewardsSelWord, cometRewardsSelBytes] using
    (evmSelectorDecode (cd := I.calldata) hsz 0xcd 0xc0 0xca 0x09
      (⟨0xcdc0ca09⟩ : UInt256) (by native_decide))

abbrev withdrawTokenPc : UInt256 := ⟨2758⟩
abbrev governorPc : UInt256 := ⟨2717⟩
abbrev rewardConfigPc : UInt256 := ⟨2615⟩
abbrev getRewardOwedPc : UInt256 := ⟨2266⟩
abbrev claimToPc : UInt256 := ⟨2044⟩
abbrev setRewardsClaimedPc : UInt256 := ⟨1723⟩
abbrev rewardsClaimedPc : UInt256 := ⟨1644⟩
abbrev setRewardConfigPc : UInt256 := ⟨1009⟩
abbrev claimPc : UInt256 := ⟨942⟩
abbrev transferGovernorPc : UInt256 := ⟨801⟩
abbrev setRewardConfigWithMultiplierPc : UInt256 := ⟨159⟩

/-! ## Body-entry stack shapes -/

/-- Stack at `withdrawToken` after the first selector arm jumps. -/
abbrev dispatchArm0Stack (I : ExecutionEnv) : List UInt256 :=
  [⟨128⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]

/-- Stack at arms 1 through 9 after the selected arm jumps. -/
abbrev dispatchArmMidStack (I : ExecutionEnv) : List UInt256 :=
  [cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]

/-- Stack at `setRewardConfigWithMultiplier`, the final arm without a trailing selector word. -/
abbrev dispatchArmLastStack (_I : ExecutionEnv) : List UInt256 :=
  [⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]

/-! ## Solm dispatch facts -/

theorem cometRewardsDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition,
      transferGovernorTransition, withdrawTokenTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, claimSelectorBytes]; rfl
    · rw [selectorOf, claimToSelectorBytes]; rfl
    · rw [selectorOf, getRewardOwedSelectorBytes]; rfl
    · rw [selectorOf, governorSelectorBytes]; rfl
    · rw [selectorOf, rewardConfigSelectorBytes]; rfl
    · rw [selectorOf, rewardsClaimedSelectorBytes]; rfl
    · rw [selectorOf, setRewardConfigSelectorBytes]; rfl
    · rw [selectorOf, setRewardConfigWithMultiplierSelectorBytes]; rfl
    · rw [selectorOf, setRewardsClaimedSelectorBytes]; rfl
    · rw [selectorOf, transferGovernorSelectorBytes]; rfl
    · rw [selectorOf, withdrawTokenSelectorBytes]; rfl) h

theorem cometRewardsDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 11 → (cometRewardsSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, claimToSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, getRewardOwedSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, governorSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, rewardConfigSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, rewardsClaimedSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, setRewardConfigSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, setRewardConfigWithMultiplierSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, setRewardsClaimedSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, transferGovernorSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, withdrawTokenSelectorBytes]
    simpa [cometRewardsSelBytes] using hnm 0 (by omega)

theorem cometRewardsBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem cometRewardsStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (fieldLoc slot 0 20 (by decide) .address) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [fieldLoc, loc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem cometRewardsStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (fieldLoc slot 0 32 (by decide) (.int uint256Int)) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [fieldLoc, loc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem cometRewardsCalldataGuard_true (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    evalExpr? config
      { contract := contract, locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.binary .lt (.arrayLength .localVar calldataGuardRef) (.intLit calldataSizeLimit)) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure, calldataGuardRef, calldataSizeLimit,
    evalBinaryOp?, readLocalPath?]
  norm_num
  omega

theorem cometRewardsCalldataGuard_false (evm : EVM.State) (locals : Store)
    (h : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    evalExpr? config
      { contract := contract, locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.binary .lt (.arrayLength .localVar calldataGuardRef) (.intLit calldataSizeLimit)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure, calldataGuardRef, calldataSizeLimit,
    evalBinaryOp?, readLocalPath?]
  norm_num
  omega

theorem cometRewardsCalldataSizeAddNot3_eq_sub4 {n : ℕ}
    (h4 : 4 ≤ n) (hn : n < UInt256.size) :
    UInt256.add (UInt256.ofNat n) (UInt256.lnot (⟨3⟩ : UInt256)) =
      UInt256.sub (UInt256.ofNat n) ⟨4⟩ := by
  apply u256_inj
  change (UInt256.ofNat n + UInt256.lnot (⟨3⟩ : UInt256)).toNat =
    (UInt256.sub (UInt256.ofNat n) ⟨4⟩).toNat
  rw [uadd_toNat]
  have hnNat : (UInt256.ofNat n).toNat = n := ulit_toNat' n hn
  have h4word : ((⟨4⟩ : UInt256).toNat = 4) := by decide
  have hlnot : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = UInt256.size - 4 := by
    unfold UInt256.lnot
    decide
  have hsub : (UInt256.sub (UInt256.ofNat n) ⟨4⟩).toNat = n - 4 := by
    rw [usub_ofNat_word_toNat (by rw [h4word]; exact h4) hn]
    rw [h4word]
  rw [hnNat, hlnot, hsub]
  have hadd : n + (UInt256.size - 4) = UInt256.size + (n - 4) := by omega
  rw [hadd, Nat.add_mod_left]
  apply Nat.mod_eq_of_lt
  omega

/-! ## Shared prefix revert traces -/

theorem cometRewardsX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode) (hsz : I.calldata.size < 4) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = cometRewardsBytecode := by
    rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable = g.subNat 0 := by
    rw [hs0]; simp [initState, Sat256.subNat]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by
    rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hrdata0 : s0.machineState.returnData = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hacc0 : (s0.createdAccounts, s0.accountMap) = (cA, σ) := by
    rw [hs0]; simp [initState]
  have hX0 :
      X (g.toNat + 1) (D_J cometRewardsBytecode 0) s0 =
        X (g.toNat + 1 - 0) (D_J cometRewardsBytecode 0) s0 := rfl
  have rd0 : RD cometRewardsBytecode I g s0 ⟨0⟩ [] ByteArray.empty
      (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := by
    exact RD.startWith (rdata := ByteArray.empty) hcode0 hpc0 hstk0 hgas0 (by omega)
      (by omega) hX0 hmem0 haw0 hrdata0 hacc0 hee0 ⟨rfl, rfl, rfl⟩
  have rd := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩, dup2, dup2,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, swap2, dup3, calldatasize, lt, iszero, push2 ⟨22⟩,
    jumpiNT (isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hsz))]
  exact (rd.solcPush1Dup1Revert0 (by decide) (by decide) (by decide) (by evm_ov) :
    RDrev cometRewardsBytecode g s0)

theorem cometRewardsX_nomatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 11 → (cometRewardsSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 :
      UInt256.eq (⟨0x01e33667⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, hnm 0 (by omega)]
  have heq1 :
      UInt256.eq (⟨0x0c340a24⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, hnm 1 (by omega)]
  have heq2 :
      UInt256.eq (⟨0x2289b6b8⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, hnm 2 (by omega)]
  have heq3 :
      UInt256.eq (⟨0x41e0cad6⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz, hnm 3 (by omega)]
  have heq4 :
      UInt256.eq (⟨0x4ff85d94⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz, hnm 4 (by omega)]
  have heq5 :
      UInt256.eq (⟨0x6394f161⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz, hnm 5 (by omega)]
  have heq6 :
      UInt256.eq (⟨0x65e12392⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq6 I hsz, hnm 6 (by omega)]
  have heq7 :
      UInt256.eq (⟨0x95e36d2c⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq7 I hsz, hnm 7 (by omega)]
  have heq8 :
      UInt256.eq (⟨0xb7034f7e⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq8 I hsz, hnm 8 (by omega)]
  have heq9 :
      UInt256.eq (⟨0xb8cc9ce6⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq9 I hsz, hnm 9 (by omega)]
  have heq10 :
      UInt256.eq (⟨0xcdc0ca09⟩ : UInt256)
          ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).shiftRight
            ⟨224⟩) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq10 I hsz, hnm 10 (by omega)]
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = cometRewardsBytecode := by
    rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable = g.subNat 0 := by
    rw [hs0]; simp [initState, Sat256.subNat]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by
    rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hrdata0 : s0.machineState.returnData = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hacc0 : (s0.createdAccounts, s0.accountMap) = (cA, σ) := by
    rw [hs0]; simp [initState]
  have hX0 :
      X (g.toNat + 1) (D_J cometRewardsBytecode 0) s0 =
        X (g.toNat + 1 - 0) (D_J cometRewardsBytecode 0) s0 := rfl
  have rd0 : RD cometRewardsBytecode I g s0 ⟨0⟩ [] ByteArray.empty
      (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := by
    exact RD.startWith (rdata := ByteArray.empty) hcode0 hpc0 hstk0 hgas0 (by omega)
      (by omega) hX0 hmem0 haw0 hrdata0 hacc0 hee0 ⟨rfl, rfl, rfl⟩
  have rd := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩, dup2, dup2,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, swap2, dup3, calldatasize, lt]
  rw [show (⟨4⟩ : UInt256) = UInt256.ofNat 4 from rfl,
    lt_four_eq_zero_of_ge hsz hsize] at rd
  have rd := evm_run rd with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := evm_run rd with [
    push2 ⟨22⟩, jumpiT one_ne_zero_uint (by native_decide), jumpdest,
    push1 ⟨0⟩, swap3, push1 ⟨224⟩, swap2, dup5, calldataload, dup4, shr, swap1,
    dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  have rd := evm_run rd with [push2 ⟨1644⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x95e36d2c⟩, eq]
  rw [heq7] at rd
  have rd := evm_run rd with [push2 ⟨1009⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb7034f7e⟩, eq]
  rw [heq8] at rd
  have rd := evm_run rd with [push2 ⟨942⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb8cc9ce6⟩, eq]
  rw [heq9] at rd
  have rd := evm_run rd with [push2 ⟨801⟩, jumpiNT (by decide),
    push4 ⟨0xcdc0ca09⟩, eq]
  rw [heq10] at rd
  have rd := evm_run rd with [push2 ⟨159⟩, jumpiNT (by decide)]
  exact (rd.solcPush1Dup1Revert0 (by decide) (by decide) (by decide) (by evm_ov) :
    RDrev cometRewardsBytecode g s0)

theorem cometRewardsReachFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨34⟩
        (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = cometRewardsBytecode := by
    rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable = g.subNat 0 := by
    rw [hs0]; simp [initState, Sat256.subNat]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by
    rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hrdata0 : s0.machineState.returnData = ByteArray.empty := by
    rw [hs0]; simp [initState]; rfl
  have hacc0 : (s0.createdAccounts, s0.accountMap) = (cA, σ) := by
    rw [hs0]; simp [initState]
  have hX0 :
      X (g.toNat + 1) (D_J cometRewardsBytecode 0) s0 =
        X (g.toNat + 1 - 0) (D_J cometRewardsBytecode 0) s0 := rfl
  have rd0 : RD cometRewardsBytecode I g s0 ⟨0⟩ [] ByteArray.empty
      (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := by
    exact RD.startWith (rdata := ByteArray.empty) hcode0 hpc0 hstk0 hgas0 (by omega)
      (by omega) hX0 hmem0 haw0 hrdata0 hacc0 hee0 ⟨rfl, rfl, rfl⟩
  have rd := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩, dup2, dup2,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, swap2, dup3, calldatasize, lt]
  rw [show (⟨4⟩ : UInt256) = UInt256.ofNat 4 from rfl,
    lt_four_eq_zero_of_ge hsz hsize] at rd
  have rd := evm_run rd with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := evm_run rd with [
    push2 ⟨22⟩, jumpiT one_ne_zero_uint (by native_decide), jumpdest,
    push1 ⟨0⟩, swap3, push1 ⟨224⟩, swap2, dup5, calldataload, dup4, shr, swap1]
  exact ⟨_, _, by simpa [hs0, dispatchArm0Stack, cometRewardsSelWord] using rd⟩

/-! ## Via-IR dispatcher reach obligations -/

theorem cometRewardsReachWithdrawToken {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 0)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
        (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨2758⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachGovernor {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 1)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) governorPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false : (cometRewardsSelBytes 0 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 1)
      (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨2717⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachRewardConfig {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 2)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) rewardConfigPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false : (cometRewardsSelBytes 0 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 2)
      (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have h1false : (cometRewardsSelBytes 1 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 2)
      (other := cometRewardsSelBytes 1) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, h1false]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨2615⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachGetRewardOwed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 3)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false : (cometRewardsSelBytes 0 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 3)
      (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have h1false : (cometRewardsSelBytes 1 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 3)
      (other := cometRewardsSelBytes 1) (by native_decide) hsel
  have h2false : (cometRewardsSelBytes 2 == I.calldata.extract 0 4) = false :=
    selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 3)
      (other := cometRewardsSelBytes 2) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, h1false]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, h2false]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq3 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨2266⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachClaimTo {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 4)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) claimToPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 4)
    (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have h1false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 4)
    (other := cometRewardsSelBytes 1) (by native_decide) hsel
  have h2false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 4)
    (other := cometRewardsSelBytes 2) (by native_decide) hsel
  have h3false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 4)
    (other := cometRewardsSelBytes 3) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, h1false]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, h2false]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz, h3false]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq4 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨2044⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachSetRewardsClaimed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 5)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        setRewardsClaimedPc (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 5)
    (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have h1false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 5)
    (other := cometRewardsSelBytes 1) (by native_decide) hsel
  have h2false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 5)
    (other := cometRewardsSelBytes 2) (by native_decide) hsel
  have h3false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 5)
    (other := cometRewardsSelBytes 3) (by native_decide) hsel
  have h4false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 5)
    (other := cometRewardsSelBytes 4) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, h1false]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, h2false]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz, h3false]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz, h4false]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq5 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨1723⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachRewardsClaimed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 6)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have h0false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 0) (by native_decide) hsel
  have h1false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 1) (by native_decide) hsel
  have h2false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 2) (by native_decide) hsel
  have h3false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 3) (by native_decide) hsel
  have h4false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 4) (by native_decide) hsel
  have h5false := selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 6)
    (other := cometRewardsSelBytes 5) (by native_decide) hsel
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz, h0false]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz, h1false]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz, h2false]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz, h3false]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz, h4false]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz, h5false]
  have heq6 : UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq6 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨1644⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachSetRewardConfig {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 7)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 0) (by native_decide) hsel]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 1) (by native_decide) hsel]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 2) (by native_decide) hsel]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 3) (by native_decide) hsel]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 4) (by native_decide) hsel]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 5) (by native_decide) hsel]
  have heq6 : UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq6 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 7)
        (other := cometRewardsSelBytes 6) (by native_decide) hsel]
  have heq7 : UInt256.eq (⟨0x95e36d2c⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq7 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  have rd := evm_run rd with [push2 ⟨1644⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x95e36d2c⟩, eq]
  rw [heq7] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨1009⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachClaim {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 8)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) claimPc
        (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 0) (by native_decide) hsel]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 1) (by native_decide) hsel]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 2) (by native_decide) hsel]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 3) (by native_decide) hsel]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 4) (by native_decide) hsel]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 5) (by native_decide) hsel]
  have heq6 : UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq6 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 6) (by native_decide) hsel]
  have heq7 : UInt256.eq (⟨0x95e36d2c⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq7 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 8)
        (other := cometRewardsSelBytes 7) (by native_decide) hsel]
  have heq8 : UInt256.eq (⟨0xb7034f7e⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq8 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  have rd := evm_run rd with [push2 ⟨1644⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x95e36d2c⟩, eq]
  rw [heq7] at rd
  have rd := evm_run rd with [push2 ⟨1009⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb7034f7e⟩, eq]
  rw [heq8] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨942⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachTransferGovernor {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 9)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        transferGovernorPc (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 0) (by native_decide) hsel]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 1) (by native_decide) hsel]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 2) (by native_decide) hsel]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 3) (by native_decide) hsel]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 4) (by native_decide) hsel]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 5) (by native_decide) hsel]
  have heq6 : UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq6 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 6) (by native_decide) hsel]
  have heq7 : UInt256.eq (⟨0x95e36d2c⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq7 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 7) (by native_decide) hsel]
  have heq8 : UInt256.eq (⟨0xb7034f7e⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq8 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 9)
        (other := cometRewardsSelBytes 8) (by native_decide) hsel]
  have heq9 : UInt256.eq (⟨0xb8cc9ce6⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq9 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  have rd := evm_run rd with [push2 ⟨1644⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x95e36d2c⟩, eq]
  rw [heq7] at rd
  have rd := evm_run rd with [push2 ⟨1009⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb7034f7e⟩, eq]
  rw [heq8] at rd
  have rd := evm_run rd with [push2 ⟨942⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb8cc9ce6⟩, eq]
  rw [heq9] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨801⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

theorem cometRewardsReachSetRewardConfigWithMultiplier {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cometRewardsBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometRewardsSelBytes 10)) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        setRewardConfigWithMultiplierPc (dispatchArmLastStack I) solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := cometRewardsReachFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize
  have heq0 : UInt256.eq (⟨0x01e33667⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq0 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 0) (by native_decide) hsel]
  have heq1 : UInt256.eq (⟨0x0c340a24⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq1 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 1) (by native_decide) hsel]
  have heq2 : UInt256.eq (⟨0x2289b6b8⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq2 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 2) (by native_decide) hsel]
  have heq3 : UInt256.eq (⟨0x41e0cad6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq3 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 3) (by native_decide) hsel]
  have heq4 : UInt256.eq (⟨0x4ff85d94⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq4 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 4) (by native_decide) hsel]
  have heq5 : UInt256.eq (⟨0x6394f161⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq5 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 5) (by native_decide) hsel]
  have heq6 : UInt256.eq (⟨0x65e12392⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq6 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 6) (by native_decide) hsel]
  have heq7 : UInt256.eq (⟨0x95e36d2c⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq7 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 7) (by native_decide) hsel]
  have heq8 : UInt256.eq (⟨0xb7034f7e⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq8 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 8) (by native_decide) hsel]
  have heq9 : UInt256.eq (⟨0xb8cc9ce6⟩ : UInt256) (cometRewardsSelWord I) = ⟨0⟩ := by
    simp [cometRewardsSelectorEq9 I hsz,
      selectorFalseOfMatch (I := I) (want := cometRewardsSelBytes 10)
        (other := cometRewardsSelBytes 9) (by native_decide) hsel]
  have heq10 : UInt256.eq (⟨0xcdc0ca09⟩ : UInt256) (cometRewardsSelWord I) = ⟨1⟩ := by
    simp [cometRewardsSelectorEq10 I hsz, hsel]
  have rd := evm_run rd with [dup2, push4 ⟨0x01e33667⟩, eq]
  rw [heq0] at rd
  have rd := evm_run rd with [push2 ⟨2758⟩, jumpiNT (by decide), pop,
    dup1, push4 ⟨0x0c340a24⟩, eq]
  rw [heq1] at rd
  have rd := evm_run rd with [push2 ⟨2717⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x2289b6b8⟩, eq]
  rw [heq2] at rd
  have rd := evm_run rd with [push2 ⟨2615⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x41e0cad6⟩, eq]
  rw [heq3] at rd
  have rd := evm_run rd with [push2 ⟨2266⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x4ff85d94⟩, eq]
  rw [heq4] at rd
  have rd := evm_run rd with [push2 ⟨2044⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x6394f161⟩, eq]
  rw [heq5] at rd
  have rd := evm_run rd with [push2 ⟨1723⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x65e12392⟩, eq]
  rw [heq6] at rd
  have rd := evm_run rd with [push2 ⟨1644⟩, jumpiNT (by decide),
    dup1, push4 ⟨0x95e36d2c⟩, eq]
  rw [heq7] at rd
  have rd := evm_run rd with [push2 ⟨1009⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb7034f7e⟩, eq]
  rw [heq8] at rd
  have rd := evm_run rd with [push2 ⟨942⟩, jumpiNT (by decide),
    dup1, push4 ⟨0xb8cc9ce6⟩, eq]
  rw [heq9] at rd
  have rd := evm_run rd with [push2 ⟨801⟩, jumpiNT (by decide),
    push4 ⟨0xcdc0ca09⟩, eq]
  rw [heq10] at rd
  exact ⟨_, _, evm_run rd with [push2 ⟨159⟩, jumpiT one_ne_zero_uint (by native_decide)]⟩

/-! ## Body-entry nonpayable reverts -/

theorem cometRewardsX_withdrawToken_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, dup6, dup6, dup5, swap3, callvalue,
    push2 ⟨938⟩, jumpiT hwv (by native_decide),
    jumpdest, dup3, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_governor_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) governorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, pop, pop, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_rewardConfig_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, dup4, dup6, dup5, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_getRewardOwed_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, swap3, swap1, swap3, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_claimTo_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimToPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, dup4, dup4, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_setRewardsClaimed_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, dup4, dup4, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_rewardsClaimed_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, pop, pop, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_setRewardConfig_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, swap1, callvalue,
    push2 ⟨797⟩, jumpiT hwv (by native_decide),
    jumpdest, dup4, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_claim_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, pop, pop, pop, callvalue,
    push2 ⟨670⟩, jumpiT hwv (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_transferGovernor_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, dup5, dup3, dup6, callvalue,
    push2 ⟨938⟩, jumpiT hwv (by native_decide),
    jumpdest, dup3, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsX_setRewardConfigWithMultiplier_callvalue_ne {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := hreach
  exact evm_run rd with [
    jumpdest, callvalue,
    push2 ⟨797⟩, jumpiT hwv (by native_decide),
    jumpdest, dup4, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

/-! ## Shared revert obligations -/

theorem cometRewardsNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 11 → (cometRewardsSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 4
  · exact (cometRewardsX_short (g := Sat256.ofUInt256 g) hcode hshort)
      |>.reEquivNoDispatch hcode (cometRewardsDispatch_none_short hshort)
  · exact (cometRewardsX_nomatch (g := Sat256.ofUInt256 g) hcode (by omega) hsize hnm)
      |>.reEquivNoDispatch hcode (cometRewardsDispatch_none_nomatch hnm)

theorem cometRewardsShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (cometRewardsX_short (g := Sat256.ofUInt256 g) hcode hsz)
    |>.reEquivNoDispatch hcode (cometRewardsDispatch_none_short hsz)

theorem cometRewardsNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I (cometRewardsSelBytes 0)
      · exact cometRewardsX_withdrawToken_callvalue_ne hwv
          (cometRewardsReachWithdrawToken hcode hsz hsize h0)
      · by_cases h1 : selIs I (cometRewardsSelBytes 1)
        · exact cometRewardsX_governor_callvalue_ne hwv
            (cometRewardsReachGovernor hcode hsz hsize h1)
        · by_cases h2 : selIs I (cometRewardsSelBytes 2)
          · exact cometRewardsX_rewardConfig_callvalue_ne hwv
              (cometRewardsReachRewardConfig hcode hsz hsize h2)
          · by_cases h3 : selIs I (cometRewardsSelBytes 3)
            · exact cometRewardsX_getRewardOwed_callvalue_ne hwv
                (cometRewardsReachGetRewardOwed hcode hsz hsize h3)
            · by_cases h4 : selIs I (cometRewardsSelBytes 4)
              · exact cometRewardsX_claimTo_callvalue_ne hwv
                  (cometRewardsReachClaimTo hcode hsz hsize h4)
              · by_cases h5 : selIs I (cometRewardsSelBytes 5)
                · exact cometRewardsX_setRewardsClaimed_callvalue_ne hwv
                    (cometRewardsReachSetRewardsClaimed hcode hsz hsize h5)
                · by_cases h6 : selIs I (cometRewardsSelBytes 6)
                  · exact cometRewardsX_rewardsClaimed_callvalue_ne hwv
                      (cometRewardsReachRewardsClaimed hcode hsz hsize h6)
                  · by_cases h7 : selIs I (cometRewardsSelBytes 7)
                    · exact cometRewardsX_setRewardConfig_callvalue_ne hwv
                        (cometRewardsReachSetRewardConfig hcode hsz hsize h7)
                    · by_cases h8 : selIs I (cometRewardsSelBytes 8)
                      · exact cometRewardsX_claim_callvalue_ne hwv
                          (cometRewardsReachClaim hcode hsz hsize h8)
                      · by_cases h9 : selIs I (cometRewardsSelBytes 9)
                        · exact cometRewardsX_transferGovernor_callvalue_ne hwv
                            (cometRewardsReachTransferGovernor hcode hsz hsize h9)
                        · by_cases h10 : selIs I (cometRewardsSelBytes 10)
                          · exact cometRewardsX_setRewardConfigWithMultiplier_callvalue_ne hwv
                              (cometRewardsReachSetRewardConfigWithMultiplier hcode hsz hsize h10)
                          · exact cometRewardsX_nomatch hcode hsz hsize (by
                              intro i hi
                              interval_cases i
                              · simpa [selIs, cometRewardsSelBytes] using h0
                              · simpa [selIs, cometRewardsSelBytes] using h1
                              · simpa [selIs, cometRewardsSelBytes] using h2
                              · simpa [selIs, cometRewardsSelBytes] using h3
                              · simpa [selIs, cometRewardsSelBytes] using h4
                              · simpa [selIs, cometRewardsSelBytes] using h5
                              · simpa [selIs, cometRewardsSelBytes] using h6
                              · simpa [selIs, cometRewardsSelBytes] using h7
                              · simpa [selIs, cometRewardsSelBytes] using h8
                              · simpa [selIs, cometRewardsSelBytes] using h9
                              · simpa [selIs, cometRewardsSelBytes] using h10)
    · exact cometRewardsX_short hcode (by omega)
  exact hrev.reEquivElim hcode fun _ _ hrevXi => by
    by_cases hdisp : dispatchMsg contract I.calldata = none
    · exact reEquiv_noDispatch hdisp hrevXi
    · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
      have htmem : t ∈ contract.transitions := by
        rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
        exact dispatchList_some_mem ht
      by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
          (transitionSignature t).paramTypes I.calldata = none
      · exact reEquiv_decodingFailed ht hdec hrevXi
      · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
        exact reEquiv_execution ht hca
          (cometRewardsBodyReverts_nonPayable t htmem
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            callargs (by simp only [initState]; exact hwv))
          (by rw [hrevXi]; exact execResultsEquiv.revert rfl rfl)

end Benchmarks.CompoundIII.CometRewards
