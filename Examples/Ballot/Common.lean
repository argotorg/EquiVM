import Examples.Ballot.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Ballot

/-! ## Ballot-wide storage and ABI helpers -/

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
-- `fromBytes'` is `Nat.ofDigits 256` over little-endian byte values.
theorem fromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- `n &&& (2^k - 1)` keeps exactly the low `k` bits.
theorem nat_land_mask_eq_mod (n k : Nat) : Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

-- LIBRARY CANDIDATE: `Reasoning.Memory` / `Reasoning.Solc`.
-- The low 20 little-endian bytes of an EVM word are the solc address-mask result.
theorem fromBytes'_take20_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 20) =
      (UInt256.land w solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits (bs.take 20), List.map_take]
  rw [← htake, hfull]
  show w.toNat % 256 ^ 20 = (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

/-- Loading a Solidity `address` stored at byte offset 0 returns the low-160-bit address word. -/
theorem ballotStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }
      = .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change .address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE]

/-- The result of applying solc's address mask is always canonical. -/
theorem solcAddrMask_result_canonical (w : UInt256) :
    (UInt256.land w solcAddrMask).toNat < EVM.addressModulus := by
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  show (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size < EVM.addressModulus
  have hle : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat := hlandle _ _
  have hltSize : Nat.land w.toNat solcAddrMask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by decide)

/-- ABI-encoding an address return is exactly the 32-byte masked address word. -/
theorem ballotAddressReturnEncoding (w : UInt256) :
    encodeReturnValue? addr (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)) := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  refine scalarReturnEncoding (t := .address) (w := UInt256.land w solcAddrMask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

end Ballot
