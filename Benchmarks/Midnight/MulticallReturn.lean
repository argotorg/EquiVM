import Benchmarks.Midnight.MulticallMemory
import Benchmarks.Midnight.RuntimeBlocks_017

/-! The shared return-data decoder and the multicall success guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (success : Bool) (hstack : R.length + 10 ≤ 1024)
    (hout : out.size < UInt256.size) (hmem : 832 ≤ mem.size) (hlower : 832 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hfit : out.size < 2^64 → out.size ≠ 0 →
      root.toNat + returnDataAllocation out.size < 2^64)
    (rd : RD midnightBytecode I g s0 ⟨3693⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: R) mem aw out σ k C) :
    ((success = false ∨ 2^64 ≤ out.size) ∧ RDrev midnightBytecode g s0) ∨
    (success = true ∧ out.size < 2^64 ∧
      MemoryPrefix mem (safeTransferOutputMem mem out root) root.toNat ∧
      memLoad (UInt256.ofNat 64) (safeTransferOutputMem mem out root) =
        safeTransferOutputPtr root out ∧
      ∃ aw' k' C', MemoryCharge (3 * ((out.size + 31) / 32)) aw aw' C C' ∧
        (MemoryCovered mem aw → MemoryCovered (safeTransferOutputMem mem out root) aw') ∧
        RD midnightBytecode I g s0 ⟨3707⟩
          ((if out.size = 0 then UInt256.ofNat 96 else root) :: R)
          (safeTransferOutputMem mem out root) aw' out σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_3693
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have h0 := MemoryCharge.refl aw C
  have hc1 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd1 (by memory_charge h0)
  by_cases hb : out.size < 2^64
  · by_cases he : out.size = 0
    · obtain ⟨k2, C2, hc2, rd2⟩ := midnightReturnDataEmptyCharge he
        (by simp only [List.length_cons]; omega) (by jump_dest) rd1
      cases success with
      | false =>
        have rr := midnightBlocks.midnight_block_3700_taken (by omega)
          (by decide) (by jump_dest) rd2
        exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_3715 (by omega) rr⟩
      | true =>
        have rd3 := midnightBlocks.midnight_block_3700_fallthrough (by omega) (by decide) rd2
        have hc12 := hc1.trans hc2
        have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3
          (by memory_charge hc12)
        refine Or.inr ⟨rfl, hb, ?_, ?_, aw, k2 + 5, C2 + 20, ?_, ?_, ?_⟩
        · simpa only [safeTransferOutputMem, if_pos he] using MemoryPrefix.refl mem root.toNat
        · simpa only [safeTransferOutputMem, safeTransferOutputPtr, if_pos he] using hfree
        · simpa only [he, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_zero] using hc3
        · intro ha
          simpa only [safeTransferOutputMem, if_pos he] using ha.mono hc3.active_le
        · simpa only [safeTransferOutputMem, if_pos he] using rd3
    · have hf := hfit hb he
      obtain ⟨aw2, k2, C2, hc2, hcover2, rd2⟩ := midnightReturnDataCopyCharge hb he hfree
        (by simp only [List.length_cons]; omega) (by jump_dest) hf rd1
      cases success with
      | false =>
        have rr := midnightBlocks.midnight_block_3700_taken (by omega)
          (by decide) (by jump_dest) rd2
        exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_3715 (by omega) rr⟩
      | true =>
        have rd3 := midnightBlocks.midnight_block_3700_fallthrough (by omega) (by decide) rd2
        have hc12 := hc1.trans hc2
        have hc3 := memoryChargeAt (work := 3 * ((out.size + 31) / 32))
          (aw₀ := aw) (C₀ := C) rd3 (by memory_charge hc12)
        have hp := returnDataMem_properties (by omega : 96 ≤ mem.size)
          (by omega : 96 ≤ root.toNat) he (by
            unfold returnDataAllocation at hf
            change _ < 2^256
            omega)
        refine Or.inr ⟨rfl, hb, ?_, ?_, aw2, k2 + 5, C2 + 20, hc3, ?_, ?_⟩
        · simpa only [safeTransferOutputMem, if_neg he] using returnDataMem_prefix he
        · simpa only [safeTransferOutputMem, safeTransferOutputPtr, if_neg he] using hp.2.1
        · intro ha
          simpa only [safeTransferOutputMem, if_neg he] using
            hcover2 (by omega) (ha.mono hc1.active_le)
        · simpa only [safeTransferOutputMem, if_neg he] using rd3
  · exact Or.inl ⟨Or.inr (by omega), midnightReturnDataOversize hout (by omega)
      (by simp only [List.length_cons]; omega) rd1⟩

end Benchmarks.Midnight
