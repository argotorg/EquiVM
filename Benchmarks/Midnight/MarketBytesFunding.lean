import Benchmarks.Midnight.MarketBytesTrace
import Benchmarks.Midnight.MarketEncoderFunding
import Benchmarks.Midnight.MemoryBufferBounds
import Benchmarks.Midnight.AllocationFunding

variable {fork : Ethereum.Fork}

/-! The market bytes encoder discharges allocation limits using its actual memory cost. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketBytesEncode_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 19 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + m.encodingSize + 32 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hgas : midnightGasBound g.toUInt256) (ha : MemoryFunding credit
      (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19181⟩
      (ptr :: (root + UInt256.ofNat 64) :: ⟨12824⟩ :: root :: ret :: root :: R)
      (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (root.toNat + m.encodingSize + 32 < 2^64 ∧
      ∃ aw' k' C', MemoryFunding (credit + 128 * m.collaterals.length) (marketBytesMemory mem root m) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (root :: R)
      (marketBytesMemory mem root m) aw' rdata σ k' C') := by
  have hword : UInt256.size = 2^256 := rfl
  have hroot : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have ha64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by dsimp only [MarketData.encodingSize] at hb; change _ < 2^256; omega)
  have hp := memoryPrefix_writeWord mem (root.toNat + 32) limit.toNat (UInt256.ofNat 32)
    (Or.inl (by omega))
  have hm1 := hm.preserve hp
  have hn : memLoad arrayPtr (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) =
      UInt256.ofNat m.collaterals.length := hm1.header.load_word ⟨0, by simp⟩ (by simp)
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightMarketEncoder_funded m
    (by simp only [List.length_cons]; omega) hm1.words hn (by simpa using hm1.header.size)
    hm1.collaterals (by have := hm.array; have := hm.extent; omega) hm.extent
    (by rw [ha64]; omega) (by
      rw [ha64]
      dsimp only [MarketData.encodingSize] at hb
      change _ < 2^256
      omega) (by jump_dest) ha rd
  have hsize := marketEncodeMemory_end
    (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) (root + UInt256.ofNat 64).toNat m
    (by rw [ha64]; dsimp only [MarketData.encodingSize] at hb; omega)
  rcases memoryAccounting_headroom rd1 ha1.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  have hfit : root.toNat + m.encodingSize + 32 < 2^64 := by
    rw [ha64] at hsize hroom
    dsimp only [MarketData.encodingSize]
    omega
  right
  refine ⟨hfit, ?_⟩
  have hend : (root + UInt256.ofNat 64) + UInt256.ofNat (288 + 128 * m.collaterals.length) =
      root + UInt256.ofNat (m.encodingSize + 32) := by
    rw [wordAddNat_add]
    congr 2
    dsimp only [MarketData.encodingSize]; omega
  have hsub : UInt256.sub ((root + UInt256.ofNat 64) +
      UInt256.ofNat (288 + 128 * m.collaterals.length)) root =
      UInt256.ofNat (m.encodingSize + 32) := by rw [hend, word_add_sub_left]
  have hlength : UInt256.ofNat (m.encodingSize + 32) + UInt256.lnot (UInt256.ofNat 31) =
      UInt256.ofNat m.encodingSize := by
    rw [addNot31_ofNat (by omega) (by change _ < 2^256; omega)]
    congr 1
  have rd2 := midnightBlocks.midnight_block_12824 (by omega)
    (by jump_dest) rd1
  have ha2 := memoryFundingAt (credit := credit + 128 * m.collaterals.length) rd2 (by
    unfold midnightBlocks.midnight_block_12824_memory
    memory_fund ha1)
  simp only [midnightBlocks.midnight_block_12824_stack,
    midnightBlocks.midnight_block_12824_memory, hsub, hlength, ha64] at rd2 ha2
  have he := marketBytesAllocationEnd m hfit
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat (m.encodingSize + 32))) =
      ⟨0⟩ := by
    rw [he]
    apply allocationCheck_ok
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightAllocate_funded
    (by simp only [List.length_cons]; omega) hc hret ha2 rd2
  rw [he] at rd3 ha3
  exact ⟨aw3, k3, C3, ha3, rd3⟩

end Benchmarks.Midnight
