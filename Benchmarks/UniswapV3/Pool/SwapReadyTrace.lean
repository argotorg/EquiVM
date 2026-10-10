import Benchmarks.UniswapV3.Pool.SwapInitAllocationTrace
import Benchmarks.UniswapV3.Pool.SwapLockTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapReadyBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2723⟩
      ([snap, ⟨0⟩, ⟨0⟩] ++ swapWords a dataStart dataLength ++ ret :: R) mem aw rdata σ k C)
    (hstate : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (ha : BoundedActiveWords aw limit)
    (hs : Slot0Memory mem snap σ ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 416 ≤ limit)
    (hperm : ee.perm = true) (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := swapInitializedMem mem p (poolProtocolDivisor (!a.zeroForOne) σ ee) a
        (storeSlot0Unlocked evm false).accountMap σ ee
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([p + UInt256.ofNat 192,
          UInt256.sgt (EVM.wordOfInt a.amountSpecified) (UInt256.ofNat 0), p, snap, ⟨0⟩, ⟨0⟩] ++
          swapWords a dataStart dataLength ++ ret :: R) mem' aw' rdata
          (storeSlot0Unlocked evm false).accountMap k' C' ∧
      HeapMemory mem' aw' ((p + UInt256.ofNat 192) + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' p.toNat ∧ Slot0Memory mem' snap σ ee ∧
      WordArrayMemory mem' p
        (swapCacheInitWords (poolProtocolDivisor (!a.zeroForOne) σ ee)
          (storeSlot0Unlocked evm false).accountMap ee) ∧ BoundedActiveWords aw' limit ∧
      ((p + UInt256.ofNat 192) + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32 := by
  have hsmall := ha.small
  obtain ⟨kl, Cl, rl⟩ := swapLockX (v := v) a.zeroForOne evm rd hstate hm hperm
    (by change R.length + 2 + 13 ≤ 1024; omega)
  have hs1 : Slot0Memory (writeWord mem 64 (p + UInt256.ofNat 192)) snap σ ee :=
    WordArrayMemory.write_disjoint hs 64 _ (Or.inl (by omega))
  have hfield : UInt256.land (UInt256.ofNat 255)
      (memLoad (UInt256.ofNat 160 + snap) (writeWord mem 64 (p + UInt256.ofNat 192))) =
      slot0FieldWord 29 1 σ ee := by
    rw [u256_add_comm, Slot0Memory.load_feeProtocol hs1
      (by change _ < 2 ^ 256; omega)]
    exact slot0FeeProtocol_clean σ ee
  obtain ⟨kf, Cf, rf⟩ := swapCacheFeeX (v := v) a.zeroForOne rl hfield
    (by change R.length + 9 + 8 ≤ 1024; omega)
  have h160 : (UInt256.ofNat 160 + snap).toNat = snap.toNat + 160 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat snap 160 (by change _ < 2 ^ 256; omega)
  have haf := BoundedActiveWords.expand32 ha
    (show (UInt256.ofNat 160 + snap).toNat + 32 ≤ limit by rw [h160]; omega)
  obtain ⟨ah, kh, Ch, rh, hah⟩ := swapCacheHeadBoundedX (v := v) rf
    (poolProtocolDivisor_clean (!a.zeroForOne) σ ee) haf (by omega)
    (by change R.length + 12 + 5 ≤ 1024; omega)
  exact swapInitAllocationBoundedX (v := v) a rh hm hah hs hsl hsb hb hov

theorem swapReadyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2723⟩
      ([snap, ⟨0⟩, ⟨0⟩] ++ swapWords a dataStart dataLength ++ ret :: R) mem aw rdata σ k C)
    (hstate : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (hs : Slot0Memory mem snap σ ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 416 ≤ 2 ^ 200)
    (hperm : ee.perm = true) (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C',
      let mem' := swapInitializedMem mem p (poolProtocolDivisor (!a.zeroForOne) σ ee) a
        (storeSlot0Unlocked evm false).accountMap σ ee
      RD (deployedRuntime v) ee g s0 ⟨2991⟩
        ([p + UInt256.ofNat 192,
          UInt256.sgt (EVM.wordOfInt a.amountSpecified) (UInt256.ofNat 0), p, snap, ⟨0⟩, ⟨0⟩] ++
          swapWords a dataStart dataLength ++ ret :: R) mem' aw' rdata
          (storeSlot0Unlocked evm false).accountMap k' C' ∧
      HeapMemory mem' aw' ((p + UInt256.ofNat 192) + UInt256.ofNat 224) ∧
      MemoryPrefix mem mem' p.toNat ∧ Slot0Memory mem' snap σ ee ∧
      WordArrayMemory mem' p
        (swapCacheInitWords (poolProtocolDivisor (!a.zeroForOne) σ ee)
          (storeSlot0Unlocked evm false).accountMap ee) := by
  obtain ⟨aw', k', C', rd', hm', hpre, hs', hc', _, _⟩ := swapReadyBoundedX (v := v)
    a evm rd hstate hm (BoundedActiveWords.of_active hm.active) hs hsl hsb hb hperm hov
  exact ⟨aw', k', C', rd', hm', hpre, hs', hc'⟩

end Benchmarks.UniswapV3.Pool
