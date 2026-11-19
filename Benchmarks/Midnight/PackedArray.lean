import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.PackedFields

/-! Shared bytecode routines locating elements of packed fixed arrays. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem uint16ArrayIndexFacts (index : UInt256) (hi : index.toNat < 7) :
    UInt256.shiftRight index (UInt256.ofNat 4) = ⟨0⟩ ∧
    UInt256.land (UInt256.shiftLeft index (UInt256.ofNat 1)) (UInt256.ofNat 30) =
      UInt256.ofNat (2 * index.toNat) ∧
    UInt256.shiftLeft (UInt256.ofNat (2 * index.toNat)) (UInt256.ofNat 3) =
      UInt256.ofNat (16 * index.toNat) := by
  have hf : ∀ i : Fin 7,
      UInt256.shiftRight (UInt256.ofNat i.val) (UInt256.ofNat 4) = ⟨0⟩ ∧
      UInt256.land (UInt256.shiftLeft (UInt256.ofNat i.val) (UInt256.ofNat 1)) (UInt256.ofNat 30) =
        UInt256.ofNat (2 * i.val) ∧
      UInt256.shiftLeft (UInt256.ofNat (2 * i.val)) (UInt256.ofNat 3) =
        UInt256.ofNat (16 * i.val) := by decide +kernel
  have hw : UInt256.ofNat index.toNat = index := u256_inj
    (UInt256.toNat_ofNat_of_lt index.val.isLt)
  simpa only [hw] using hf ⟨index.toNat, hi⟩

theorem midnightUint16ArrayLocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot index ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hi : index.toNat < 7) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19133⟩ (slot :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.ofNat (2 * index.toNat) :: slot :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.lt index ⟨7⟩) = ⟨0⟩ := by
    rw [ult_one hi]; rfl
  have rd1 := midnightBlocks.midnight_block_19133_fallthrough (by omega) hc rd
  simp only [midnightBlocks.midnight_block_19133_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19146 hstack hret rd1
  simp only [midnightBlocks.midnight_block_19146_stack, (uint16ArrayIndexFacts index hi).1,
    (uint16ArrayIndexFacts index hi).2.1] at rd2
  have hz : (⟨0⟩ : UInt256) + slot = slot := by
    apply u256_inj
    rw [uadd_toNat]
    change (0 + slot.toNat) % UInt256.size = slot.toNat
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt slot.val.isLt
  rw [hz] at rd2
  exact ⟨_, _, rd2⟩

theorem uint128ArrayIndexFacts (index : UInt256) (hi : index.toNat < 128) :
    UInt256.shiftRight index (UInt256.ofNat 1) = UInt256.ofNat (index.toNat / 2) ∧
    UInt256.land (UInt256.shiftLeft index (UInt256.ofNat 4)) (UInt256.ofNat 16) =
      UInt256.ofNat (16 * (index.toNat % 2)) ∧
    UInt256.shiftLeft (UInt256.ofNat (16 * (index.toNat % 2))) (UInt256.ofNat 3) =
      UInt256.ofNat (128 * (index.toNat % 2)) := by
  have hf : ∀ i : Fin 128,
      UInt256.shiftRight (UInt256.ofNat i.val) (UInt256.ofNat 1) = UInt256.ofNat (i.val / 2) ∧
      UInt256.land (UInt256.shiftLeft (UInt256.ofNat i.val) (UInt256.ofNat 4)) (UInt256.ofNat 16) =
        UInt256.ofNat (16 * (i.val % 2)) ∧
      UInt256.shiftLeft (UInt256.ofNat (16 * (i.val % 2))) (UInt256.ofNat 3) =
        UInt256.ofNat (128 * (i.val % 2)) := by native_decide
  simpa only [u256_ofNat_toNat] using hf ⟨index.toNat, hi⟩

theorem midnightUint128ArrayLocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot index ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hi : index.toNat < 128) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19480⟩ (slot :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret
      (UInt256.ofNat (16 * (index.toNat % 2)) :: (slot + UInt256.ofNat (index.toNat / 2)) :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.lt index ⟨128⟩) = ⟨0⟩ := by
    rw [ult_one hi]; rfl
  have rd1 := midnightBlocks.midnight_block_19480_fallthrough (by omega) hc rd
  simp only [midnightBlocks.midnight_block_19480_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19493 hstack hret rd1
  simp only [midnightBlocks.midnight_block_19493_stack, (uint128ArrayIndexFacts index hi).1,
    (uint128ArrayIndexFacts index hi).2.1, u256_add_comm _ slot] at rd2
  exact ⟨_, _, rd2⟩

end Benchmarks.Midnight
