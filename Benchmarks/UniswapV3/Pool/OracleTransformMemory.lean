import Benchmarks.UniswapV3.Pool.ObservationMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_062

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: low-field masking commutes with an EVM left shift.
theorem shiftLeft_mask32_128 (w : UInt256) :
    UInt256.land (UInt256.shiftLeft w (UInt256.ofNat 128))
      (UInt256.ofNat 1461501636990620551282746369252908412224164331520) =
    UInt256.shiftLeft (UInt256.land w (UInt256.ofNat (2 ^ 32 - 1))) ⟨128⟩ := by
  have hm : (UInt256.ofNat 1461501636990620551282746369252908412224164331520).toNat =
      (2 ^ 32 - 1) <<< 128 := by decide
  have hlo : (UInt256.land w (UInt256.ofNat (2 ^ 32 - 1))).toNat < 2 ^ 32 :=
    u256LandMaskToNatLtOfToNat _ _ (by decide)
  apply u256_inj
  rw [uland_toNat, hm, shiftLeft_toNat_of_noOverflow (UInt256.land w (UInt256.ofNat (2 ^ 32 - 1))) _ (by decide) (by
    change _ * 2 ^ 128 < 2 ^ 256; omega)]
  have hs : (UInt256.shiftLeft w (UInt256.ofNat 128)).toNat =
      (w.toNat <<< 128) % 2 ^ 256 := rfl
  rw [hs, ← nat_land_mask_eq_mod _ 256]
  change ((w.toNat <<< 128) &&& (2 ^ 256 - 1)) &&& ((2 ^ 32 - 1) <<< 128) = _
  rw [Nat.and_right_comm]
  change Nat.land ((w.toNat <<< 128) &&& ((2 ^ 32 - 1) <<< 128)) (2 ^ 256 - 1) = _
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right
    (show ((2 ^ 32 - 1) <<< 128) < 2 ^ 256 by decide))]
  rw [← Nat.shiftLeft_and_distrib, Nat.shiftLeft_eq, uland_toNat]
  rfl

def oracleTransformHeadMem (mem : ByteArray) (p : UInt256)
    (last : OracleObservation) (time : UInt256) (tick : Int) (liquidity : UInt256) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + ⟨128⟩)) p.toNat
    [time, EVM.wordOfInt (oracleTransformed last time tick liquidity).tickCumulative]

theorem oracleTransformHeadMem_prefix (mem : ByteArray) (p : UInt256)
    (last : OracleObservation) (time : UInt256) (tick : Int) (liquidity : UInt256) :
    MemoryPrefix mem (oracleTransformHeadMem mem p last time tick liquidity) p.toNat :=
  (memoryPrefix_sparse_writeWord mem 64 p.toNat _ (Or.inr (by decide))).trans
    (writeWordArray_prefix _ _ _ _ (le_refl _))

theorem oracleTransformHeadMem_write (mem : ByteArray) (p : UInt256)
    (last : OracleObservation) (time : UInt256) (tick : Int) (liquidity : UInt256) :
    writeWord (writeWord (oracleTransformHeadMem mem p last time tick liquidity)
      (p.toNat + 64) (oracleTransformed last time tick liquidity).secondsPerLiquidity)
      (p.toNat + 96) ⟨1⟩ =
    wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words := by
  rfl


theorem oracleDelta_mask_time (time previous : UInt256) :
    oracleDelta (UInt256.land time (UInt256.ofNat (2 ^ 32 - 1))) previous =
      oracleDelta time previous := by
  apply u256_inj
  apply Int.ofNat_inj.mp
  change Int.ofNat (oracleDelta (UInt256.land time (UInt256.ofNat (2 ^ 32 - 1))) previous).toNat =
    Int.ofNat (oracleDelta time previous).toNat
  rw [← oracleDelta_source, ← oracleDelta_source,
    ← normalizeUIntWord_mask ⟨32, by decide⟩ time _ (by decide)]
  change ((Int.ofNat time.toNat % Int.ofNat (EVM.twoPow 32)) -
    Int.ofNat previous.toNat) % Int.ofNat (EVM.twoPow 32) =
    (Int.ofNat time.toNat - Int.ofNat previous.toNat) % Int.ofNat (EVM.twoPow 32)
  rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]

theorem ObservationMemory.load_timestamp {mem : ByteArray} {p : UInt256}
    {last : OracleObservation} (hm : ObservationMemory mem p last)
    (hb : p.toNat + 128 < UInt256.size) : memLoad p mem = last.timestamp := by
  simpa only [OracleObservation.words, List.getElem_cons_zero, Nat.mul_zero, show p + UInt256.ofNat 0 = p from u256_add_zero p]
    using hm.load 0 (by change 0 < 4; decide) hb

theorem ObservationMemory.load_tick {mem : ByteArray} {p : UInt256}
    {last : OracleObservation} (hm : ObservationMemory mem p last)
    (hb : p.toNat + 128 < UInt256.size) :
    memLoad (p + UInt256.ofNat 32) mem = EVM.wordOfInt last.tickCumulative :=
  hm.load 1 (by change 1 < 4; decide) hb

theorem ObservationMemory.load_seconds {mem : ByteArray} {p : UInt256}
    {last : OracleObservation} (hm : ObservationMemory mem p last)
    (hb : p.toNat + 128 < UInt256.size) :
    memLoad (p + UInt256.ofNat 64) mem = last.secondsPerLiquidity :=
  hm.load 2 (by change 2 < 4; decide) hb

theorem oracleTransformHeadMem_eq {mem : ByteArray} {aw p lastPtr : UInt256}
    {last : OracleObservation} {time timeRaw tickRaw liquidity : UInt256} {tick : Int}
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem lastPtr last)
    (hp : 96 ≤ lastPtr.toNat) (hl : lastPtr.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 128 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick) :
    uniswapV3Pool_block_18474_taken_memory (mem := mem) (x2 := tickRaw)
      (x3 := timeRaw) (x4 := lastPtr) =
    oracleTransformHeadMem mem p last time tick liquidity := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hh.load64
  have hlb : lastPtr.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have htime' : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time := by
    rw [u256_land_comm]; exact htime
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hpre : MemoryPrefix mem
      (writeWord (writeWord mem 64 (p + ⟨128⟩)) p.toNat time) p.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 p.toNat _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ p.toNat p.toNat time (Or.inl (le_refl _)))
  have hm' : ObservationMemory
      (writeWord (writeWord mem 64 (p + ⟨128⟩)) p.toNat time) lastPtr last :=
    MemoryPrefix.wordArray hpre hm hp hl
  have hzero : UInt256.ofNat 0 + lastPtr = lastPtr := u256_zero_add lastPtr
  have hl0 := hm.load_timestamp hlb
  have hl32 := hm'.load_tick hlb
  have hd : UInt256.land (UInt256.ofNat 4294967295) (UInt256.sub timeRaw last.timestamp) =
      oracleDelta time last.timestamp := by
    rw [u256_land_comm]
    change oracleDelta timeRaw last.timestamp = _
    rw [← oracleDelta_mask_time, htime]
  simp only [uniswapV3Pool_block_18474_taken_memory, hload, hzero,
    u256_add_comm (UInt256.ofNat 128) p, u256_add_comm (UInt256.ofNat 32) p,
    u256_add_comm (UInt256.ofNat 32) lastPtr, htime', hl0, htick, hd, hp32]
  change writeWord
    (writeWord (writeWord mem 64 (p + ⟨128⟩)) p.toNat time) (p.toNat + 32)
    (UInt256.signextend (UInt256.ofNat 6)
      (memLoad (lastPtr + UInt256.ofNat 32)
        (writeWord (writeWord mem 64 (p + ⟨128⟩)) p.toNat time) +
       UInt256.mul (EVM.wordOfInt tick) (oracleDelta time last.timestamp))) = _
  rw [hl32, ← oracleTransformed_tick_word last time tick liquidity]
  rfl


theorem oracleTransformTailMem_eq {mem : ByteArray} {p lastPtr : UInt256}
    {last : OracleObservation} {time liquidity : UInt256} {tick : Int}
    (hm : ObservationMemory mem lastPtr last) (hp : 96 ≤ lastPtr.toNat)
    (hl : lastPtr.toNat + 128 ≤ p.toNat) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_18603_memory
      (mem := oracleTransformHeadMem mem p last time tick liquidity)
      (x0 := UInt256.shiftLeft (oracleDelta time last.timestamp) ⟨128⟩)
      (x1 := oracleLiquidityDenominator liquidity)
      (x2 := p + UInt256.ofNat 64) (x9 := lastPtr) =
    wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words := by
  have hm' : ObservationMemory (oracleTransformHeadMem mem p last time tick liquidity) lastPtr last :=
    MemoryPrefix.wordArray (oracleTransformHeadMem_prefix mem p last time tick liquidity) hm hp hl
  have hload := hm'.load_seconds (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hadd : UInt256.ofNat 32 + (p + UInt256.ofNat 64) = p + UInt256.ofNat 96 := by
    rw [u256_add_comm (UInt256.ofNat 32), uadd_assoc]; rfl
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  have hone : UInt256.isZero (UInt256.isZero (UInt256.ofNat 1)) = (⟨1⟩ : UInt256) := by decide
  simp only [uniswapV3Pool_block_18603_memory, u256_add_comm (UInt256.ofNat 64) lastPtr,
    hload, hadd, hp64, hp96, hmask, hone, u256_land_comm (UInt256.ofNat (2 ^ 160 - 1))]
  exact oracleTransformHeadMem_write mem p last time tick liquidity

end Benchmarks.UniswapV3.Pool


