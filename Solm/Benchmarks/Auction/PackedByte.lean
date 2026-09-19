import Solm.Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the uint8 cleanup check and its canonicality condition.
theorem lowByteClean {value : UInt256} (hc : value.toNat < 256) :
    UInt256.land value ⟨255⟩ = value := by
  apply u256_inj
  rw [uland_toNat]
  change Nat.land value.toNat (2 ^ 8 - 1) = value.toNat
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt hc

theorem lowByteClean_iff (value : UInt256) :
    UInt256.land value ⟨255⟩ = value ↔ value.toNat < 256 := by
  constructor
  · intro h
    rw [← h]
    exact lowByte_bound value
  · exact lowByteClean

-- GENERALIZES Reasoning.Theory.storageLocStore_bool_true_offset0 to an arbitrary byte.
theorem storageLocStore_uint8 (evm : EVM.State) (slot value : UInt256)
    (hc : value.toNat < 256) :
    storageLocStore evm
      { slot := slot, offset := 0, size := 1, hbound := by decide,
        type := .int (.uint ⟨8, by decide⟩) }
      (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) value)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof value).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 1) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask value 1 (by decide),
    fromBytes'_drop_wordLE]
  rw [u256_lor_toNat, packedSetFalseWord_toNat]
  rw [nat_lor_comm]
  rw [show 256 = 2 ^ 8 by decide, Nat.mul_comm (2 ^ 8)]
  rw [nat_lor_shift_add value.toNat _ 8 hc]
  have hbound := (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [Nat.mod_eq_of_lt (show value.toNat +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 8 * 2 ^ 8 <
        UInt256.size from by
      change _ < 2 ^ 256
      change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256
        at hbound
      omega)]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof value).2]
  change (UInt256.land value ⟨255⟩).toNat +
    256 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 256) = _
  rw [lowByteClean hc]
  omega

end Auction
