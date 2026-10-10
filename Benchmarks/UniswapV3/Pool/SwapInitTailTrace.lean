import Benchmarks.UniswapV3.Pool.SwapStateAllocation
import Benchmarks.UniswapV3.Pool.SwapEntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapInitTailBoundedX {limit : Nat} {σ σsnap : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q cache snap fee exactWord dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, slot0FieldWord 0 20 σsnap ee,
        q + UInt256.ofNat 64, q, ⟨0⟩, exactWord, cache, snap, ⟨0⟩, ⟨0⟩] ++
        swapWords a dataStart dataLength ++ ret :: R)
      (swapStateHeadMem mem q (EVM.wordOfInt a.amountSpecified)) aw rdata σ k C)
    (ha : BoundedActiveWords aw limit) (hq : 128 ≤ q.toNat) (hb : q.toNat + 224 ≤ limit)
    (hc : WordArrayMemory mem cache (swapCacheInitWords fee σ ee))
    (hcl : 96 ≤ cache.toNat) (hcb : cache.toNat + 192 ≤ q.toNat)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ q.toNat) (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := wordArrayAllocMem mem q
        (swapStateInitWords (EVM.wordOfInt a.amountSpecified) (slot0FieldWord 0 20 σsnap ee)
          (EVM.wordOfInt (slot0TickValue σsnap ee)) (feeGrowthWord (!a.zeroForOne) σ ee)
          (poolLiquidityWord σ ee))
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([q, exactWord, cache, snap, ⟨0⟩, ⟨0⟩] ++ swapWords a dataStart dataLength ++ ret :: R)
        mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' (q + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' q.toNat ∧ BoundedActiveWords aw' limit ∧
      (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32 := by
  have hsmall := ha.small
  have hfit : q.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have h64 := uadd_word_ofNat_toNat q 64 (by omega)
  have h128 := uadd_word_ofNat_toNat q 128 (by omega)
  let price := slot0FieldWord 0 20 σsnap ee
  let tick := EVM.wordOfInt (slot0TickValue σsnap ee)
  let remaining := EVM.wordOfInt a.amountSpecified
  let growth := feeGrowthWord (!a.zeroForOne) σ ee
  let mh := swapStateHeadMem mem q remaining
  have hpreH : MemoryPrefix mem mh q.toNat := swapStateHeadMem_prefix mem q remaining (by omega)
  have hsH : Slot0Memory mh snap σsnap ee := MemoryPrefix.wordArray hpreH hs hsl hsb
  have hsP : Slot0Memory (writeWord mh (q + UInt256.ofNat 64).toNat price) snap σsnap ee :=
    WordArrayMemory.write_disjoint hsH _ _ (Or.inr (by rw [h64]; exact Nat.le_trans hsb (by omega)))
  have ht : memLoad (UInt256.ofNat 32 + snap)
      (writeWord mh (q + UInt256.ofNat 64).toNat price) = tick := by
    rw [u256_add_comm]
    exact Slot0Memory.load_tick hsP (by omega)
  obtain ⟨am, km, Cm, rm, ham⟩ := swapStateMiddleBoundedX (v := v) a.zeroForOne rd
    (slot0Price_clean σsnap ee) ht (slot0TickWord_idem σsnap ee) ha
    (by rw [h64]; omega) (by omega) (by change R.length + 2 + 17 ≤ 1024; omega)
  have hcursor : UInt256.ofNat 32 + (UInt256.ofNat 32 + (q + UInt256.ofNat 64)) =
      q + UInt256.ofNat 128 := by
    rw [u256_add_comm (UInt256.ofNat 32) (q + UInt256.ofNat 64), u256_add_assoc,
      u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
    rfl
  rw [hcursor] at rm
  let mm := swapStateMiddleMem mh (q + UInt256.ofNat 64) price tick
  have hpreM : MemoryPrefix mem mm q.toNat := hpreH.trans
    ((swapStateMiddleMem_prefix mh (q + UInt256.ofNat 64) price tick
      (by rw [h64]; omega)).mono (by rw [h64]; omega))
  have hcM : WordArrayMemory mm cache (swapCacheInitWords fee σ ee) :=
    MemoryPrefix.wordArray hpreM hc hcl hcb
  have h160 : (UInt256.ofNat 32 + (q + UInt256.ofNat 128)).toNat = q.toNat + 160 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h128]; omega), h128]
  have hcG := WordArrayMemory.write_disjoint hcM (q + UInt256.ofNat 128).toNat growth
    (Or.inr (by change cache.toNat + 192 ≤ _; rw [h128]; omega))
  have hcP := WordArrayMemory.write_disjoint hcG (UInt256.ofNat 32 +
    (q + UInt256.ofNat 128)).toNat (⟨0⟩ : UInt256)
    (Or.inr (by change cache.toNat + 192 ≤ _; rw [h160]; omega))
  have hliq := WordArrayMemory.load hcP 1 (by change 1 < 6; decide)
    (by change cache.toNat + 192 < UInt256.size; omega)
  have hl : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (memLoad (UInt256.ofNat 32 + cache)
        (writeWord (writeWord mm (q + UInt256.ofNat 128).toNat growth)
          (UInt256.ofNat 32 + (q + UInt256.ofNat 128)).toNat ⟨0⟩)) =
      poolLiquidityWord σ ee := by
    rw [u256_add_comm (UInt256.ofNat 32) cache, hliq, u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) (poolLiquidityWord_lt σ ee)
  obtain ⟨ar, kr, Cr, rr, har, hcover⟩ := swapStateTailBoundedX (v := v) rm hl ham
    (by rw [h128]; omega) (by omega) (by change R.length + 10 + 9 ≤ 1024; omega)
  have hmem :=
    swapStateAllocation_eq mem q remaining price tick growth (poolLiquidityWord σ ee) hfit
  change swapStateTailMem mm (q + UInt256.ofNat 128) growth (poolLiquidityWord σ ee) = _ at hmem
  rw [hmem] at rr
  refine ⟨ar, kr, Cr, rr, ?_, wordArrayAllocMem_prefix mem q _, har, ?_⟩
  · exact wordArrayAllocMem_heap mem q ar _ hq (by simp [swapStateInitWords])
      (hb.trans hsmall) har.active
  · rw [h128] at hcover
    rw [uadd_word_ofNat_toNat q 224 hfit]
    omega

theorem swapInitTailX {σ σsnap : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q cache snap fee exactWord dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, slot0FieldWord 0 20 σsnap ee,
        q + UInt256.ofNat 64, q, ⟨0⟩, exactWord, cache, snap, ⟨0⟩, ⟨0⟩] ++
        swapWords a dataStart dataLength ++ ret :: R)
      (swapStateHeadMem mem q (EVM.wordOfInt a.amountSpecified)) aw rdata σ k C)
    (ha : ActiveWords aw) (hq : 128 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hc : WordArrayMemory mem cache (swapCacheInitWords fee σ ee))
    (hcl : 96 ≤ cache.toNat) (hcb : cache.toNat + 192 ≤ q.toNat)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ q.toNat) (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := wordArrayAllocMem mem q
        (swapStateInitWords (EVM.wordOfInt a.amountSpecified) (slot0FieldWord 0 20 σsnap ee)
          (EVM.wordOfInt (slot0TickValue σsnap ee)) (feeGrowthWord (!a.zeroForOne) σ ee)
          (poolLiquidityWord σ ee))
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([q, exactWord, cache, snap, ⟨0⟩, ⟨0⟩] ++ swapWords a dataStart dataLength ++ ret :: R)
        mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' (q + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' q.toNat := by
  obtain ⟨aw', k', C', rd', hm', hpre, _, _⟩ := swapInitTailBoundedX (v := v)
    a rd (BoundedActiveWords.of_active ha) hq hb hc hcl hcb hs hsl hsb hov
  exact ⟨aw', k', C', rd', hm', hpre⟩

end Benchmarks.UniswapV3.Pool
