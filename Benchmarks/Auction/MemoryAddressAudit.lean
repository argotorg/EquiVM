import Benchmarks.Auction.DynamicMemory

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Auction

set_option maxRecDepth 4096 in
theorem auctionMemoryAddressAudit_write_size (v : UInt256) :
    (v.toByteArray.write 0 ByteArray.empty (USize.size + 320) 32).size = 352 := by
  have hsmall : 320 < USize.size := lt_usize _ (by norm_num)
  have hpad : (USize.ofNat (USize.size + 320)).toNat = 320 := by
    rw [USize.toNat_ofNat']
    change (USize.size + 320) % USize.size = 320
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hsmall]
  have hv : v.toByteArray.data.size = 32 := toByteArray_size v
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ (32 : Nat) = 0),
    if_neg (by rw [toByteArray_size]; omega)]
  change (ByteArray.copySlice _ _ _ _ _).data.size = 352
  simp only [ByteArray.data_copySlice, ByteArray.data_append, Array.size_append,
    Array.size_extract, ByteArray.size_empty, hv, Nat.sub_zero, Nat.zero_add]
  simp only [ffi.ByteArray.zeroes, Array.size_replicate]
  simp only [toByteArray_size, Nat.min_self, Nat.zero_min, Nat.zero_sub,
    Nat.add_zero, show ByteArray.empty.data.size = 0 from rfl,
    show ({ toBitVec := ↑(USize.size + 320) } : USize).toNat = 320 from hpad,
    show ({ toBitVec := ↑(0 : Nat) } : USize).toNat = 0 from rfl, Nat.zero_add]
  omega

set_option maxRecDepth 4096 in
theorem auctionMemoryAddressAudit_store_load :
    let ptr := UInt256.ofNat (USize.size + 320)
    let mem : MachineState := default
    let stored := mem.mstore ptr ⟨1⟩
    stored.memory.size = 352 ∧ stored.lookupMemory ptr = ⟨0⟩ := by
  intro ptr mem stored
  have hptr : ptr.toNat = USize.size + 320 := by
    apply UInt256.toNat_ofNat_of_lt
    have hb := USize.size_le
    norm_num [UInt256.size] at hb ⊢
    omega
  have hsize : stored.memory.size = 352 := by
    change ((⟨1⟩ : UInt256).toByteArray.write 0 ByteArray.empty ptr.toNat 32).size = 352
    rw [hptr]
    exact auctionMemoryAddressAudit_write_size _
  refine ⟨hsize, ?_⟩
  unfold MachineState.lookupMemory
  rw [hsize, hptr]
  have hb := USize.le_size
  rw [if_pos (Or.inl (by norm_num at hb; omega))]

theorem auctionMemoryAddressAudit_memoryCost :
    Cₘ (UInt256.ofNat (MachineState.M 0 (2 ^ 64 + 320) 32)) + 3 < UInt256.size := by
  decide

end Auction
