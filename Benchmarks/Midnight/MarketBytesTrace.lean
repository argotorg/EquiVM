import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.MarketEncoder
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.RuntimeBlocks_048

/-! The shared ABI encoder and dynamic-bytes allocation tail used for market hashing. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem addNot31_ofNat {size : Nat} (hlo : 32 ≤ size) (hhi : size < UInt256.size) :
    UInt256.ofNat size + UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat (size - 32) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hhi,
    show (UInt256.lnot (UInt256.ofNat 31)).toNat = 2^256 - 32 from by native_decide,
    UInt256.toNat_ofNat_of_lt (by omega)]
  norm_num only [UInt256.size] at hhi ⊢
  omega

theorem marketBytesAllocationEnd {root : UInt256} (m : MarketData)
    (hb : root.toNat + m.encodingSize + 32 < 2^64) :
    allocationEnd root (UInt256.ofNat (m.encodingSize + 32)) =
      root + UInt256.ofNat (m.encodingSize + 32) := by
  have hs : (UInt256.ofNat (m.encodingSize + 32)).toNat = m.encodingSize + 32 :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hr : (m.encodingSize + 32 + 31) / 32 * 32 = m.encodingSize + 32 := by
    dsimp only [MarketData.encodingSize]; omega
  apply u256_inj
  rw [allocationEnd_toNat (by rw [hs]; change _ < 2^256; omega)
    (by rw [hs, hr]; change _ < 2^256; omega), hs, hr,
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]

set_option maxRecDepth 2000000 in
theorem midnightMarketBytesEncode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 19 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + m.encodingSize + 32 < 2^64)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19181⟩
      (ptr :: (root + UInt256.ofNat 64) :: ⟨12824⟩ :: root :: ret :: root :: R)
      (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret (root :: R)
      (marketBytesMemory mem root m) aw' rdata σ k' C' := by
  have hroot : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have ha64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by dsimp only [MarketData.encodingSize] at hb; change _ < 2^256; omega)
  have hp := memoryPrefix_writeWord mem (root.toNat + 32) limit.toNat (UInt256.ofNat 32)
    (Or.inl (by omega))
  have hm1 := hm.preserve hp
  have hn : memLoad arrayPtr (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) =
      UInt256.ofNat m.collaterals.length := hm1.header.load_word ⟨0, by simp⟩ (by simp)
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightMarketEncoder m
    (by simp only [List.length_cons]; omega) hm1.words hn (by simpa using hm1.header.size)
    hm1.collaterals (by have := hm.array; have := hm.extent; omega) hm.extent
    (by rw [ha64]; omega) (by
      rw [ha64]
      dsimp only [MarketData.encodingSize] at hb
      change _ < 2^256
      omega) (by jump_dest) rd
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
  simp only [midnightBlocks.midnight_block_12824_stack,
    midnightBlocks.midnight_block_12824_memory, hsub, hlength, ha64] at rd2
  have he := marketBytesAllocationEnd m hb
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat (m.encodingSize + 32))) =
      ⟨0⟩ := by
    rw [he]
    apply allocationCheck_ok
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
  obtain ⟨aw3, k3, C3, rd3⟩ := midnightAllocate
    (by simp only [List.length_cons]; omega) hc hret rd2
  rw [he] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

end Benchmarks.Midnight
