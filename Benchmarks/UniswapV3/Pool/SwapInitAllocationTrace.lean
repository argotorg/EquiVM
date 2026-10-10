import Benchmarks.UniswapV3.Pool.SwapInitHeadTrace
import Benchmarks.UniswapV3.Pool.SwapInitTailTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapInitializedMem (mem : ByteArray) (p fee : UInt256) (a : SwapArgs)
    (σ σsnap : AccountMap) (I : ExecutionEnv) : ByteArray :=
  wordArrayAllocMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ I))
    (p + UInt256.ofNat 192)
    (swapStateInitWords (EVM.wordOfInt a.amountSpecified) (slot0FieldWord 0 20 σsnap I)
      (EVM.wordOfInt (slot0TickValue σsnap I)) (feeGrowthWord (!a.zeroForOne) σ I)
      (poolLiquidityWord σ I))

theorem swapInitAllocationBoundedX {limit : Nat} {σ σsnap : AccountMap}
    {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw aw0 p snap fee dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2822⟩
      ([UInt256.ofNat ee.header.timestamp, UInt256.ofNat 64 + p, p, ⟨0⟩, snap, ⟨0⟩, ⟨0⟩] ++
        swapWords a dataStart dataLength ++ ret :: R)
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ ee)
      aw rdata σ k C)
    (hm : HeapMemory mem aw0 p) (ha : BoundedActiveWords aw limit)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 416 ≤ limit)
    (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := swapInitializedMem mem p fee a σ σsnap ee
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([p + UInt256.ofNat 192,
          UInt256.sgt (EVM.wordOfInt a.amountSpecified) (UInt256.ofNat 0), p, snap, ⟨0⟩, ⟨0⟩] ++
          swapWords a dataStart dataLength ++ ret :: R) mem' aw' rdata σ k' C' ∧
      HeapMemory mem' aw' ((p + UInt256.ofNat 192) + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' p.toNat ∧ Slot0Memory mem' snap σsnap ee ∧
      WordArrayMemory mem' p (swapCacheInitWords fee σ ee) ∧ BoundedActiveWords aw' limit ∧
      ((p + UInt256.ofNat 192) + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32 := by
  have hsmall := ha.small
  obtain ⟨ah, kh, Ch, rh, hah⟩ := swapInitHeadBoundedX (v := v) rd hm ha hs hsl hsb (by omega)
    (by change R.length + 3 + 15 ≤ 1024; omega)
  have h192 := uadd_word_ofNat_toNat p 192
    (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  have hc := wordArrayAllocMem_region mem p (swapCacheInitWords fee σ ee) hm.lower
    (by simp [swapCacheInitWords])
  have hp := wordArrayAllocMem_prefix mem p (swapCacheInitWords fee σ ee)
  have hsc : Slot0Memory (wordArrayAllocMem mem p (swapCacheInitWords fee σ ee)) snap σsnap ee :=
    MemoryPrefix.wordArray hp hs hsl hsb
  obtain ⟨ar, kr, Cr, rr, hmr, hpre, har, hcover⟩ := swapInitTailBoundedX (v := v) a rh hah
    (by rw [h192]; have hlo := hm.lower; omega) (by rw [h192]; omega)
    hc (by have hlo := hm.lower; omega) (by rw [h192]) hsc hsl (by rw [h192]; omega) hov
  have hpreOrig := hp.trans (hpre.mono (by rw [h192]; omega))
  refine ⟨ar, kr, Cr, rr, hmr, hpreOrig,
    MemoryPrefix.wordArray hpreOrig hs hsl hsb, ?_, har, hcover⟩
  exact MemoryPrefix.wordArray hpre hc (by have hlo := hm.lower; omega)
    (by change p.toNat + 192 ≤ _; rw [h192])

theorem swapInitAllocationX {σ σsnap : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw aw0 p snap fee dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2822⟩
      ([UInt256.ofNat ee.header.timestamp, UInt256.ofNat 64 + p, p, ⟨0⟩, snap, ⟨0⟩, ⟨0⟩] ++
        swapWords a dataStart dataLength ++ ret :: R)
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ ee)
      aw rdata σ k C)
    (hm : HeapMemory mem aw0 p) (ha : ActiveWords aw)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 416 ≤ 2 ^ 200)
    (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := swapInitializedMem mem p fee a σ σsnap ee
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([p + UInt256.ofNat 192,
          UInt256.sgt (EVM.wordOfInt a.amountSpecified) (UInt256.ofNat 0), p, snap, ⟨0⟩, ⟨0⟩] ++
          swapWords a dataStart dataLength ++ ret :: R) mem' aw' rdata σ k' C' ∧
      HeapMemory mem' aw' ((p + UInt256.ofNat 192) + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' p.toNat ∧ Slot0Memory mem' snap σsnap ee ∧
      WordArrayMemory mem' p (swapCacheInitWords fee σ ee) := by
  obtain ⟨aw', k', C', rd', hm', hpre, hs', hc', _, _⟩ := swapInitAllocationBoundedX (v := v)
    a rd hm (BoundedActiveWords.of_active ha) hs hsl hsb hb hov
  exact ⟨aw', k', C', rd', hm', hpre, hs', hc'⟩

end Benchmarks.UniswapV3.Pool
