import Benchmarks.Auction.MintPrefix
import Benchmarks.Auction.CallOutput
import Benchmarks.Auction.MemoryGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def mintCallMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  callOutputMem (selectorMem mem ptr mintWord) out ptr ⟨32⟩

def mintCallWords (aw ptr : UInt256) : UInt256 :=
  callActiveWords (expandedWords aw ptr ⟨32⟩) ptr ⟨4⟩ ptr ⟨32⟩

theorem mintCall {I g s0 ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨3000⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hov : R.length + 13 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0
        mintSelector (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨3071⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: ret :: R)
        (mintCallMem mem out ptr) (mintCallWords aw ptr) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd3066⟩ := mintPrefix h hm hb hov
  have hcd : (selectorMem mem ptr mintWord).readWithPadding ptr.toNat 4 = mintSelector := by
    rw [selectorMem_read hm, mintWord_prefix]
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd3067, ho⟩ :=
    callBridge rd3066 hs hperm (by native_decide) hcd (by decide) (by evm_ov)
  exact ⟨evm', cA', σ', z, out, _, _, hc, hs',
    evm_run rd3067 with [swap3, pop, pop, pop], ho⟩

theorem mintCallMem_size {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (out : ByteArray) (ho : out.size < UInt256.size) :
    (mintCallMem mem out ptr).size = max mem.size (ptr.toNat + 32) := by
  have hsz : (selectorMem mem ptr mintWord).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size _ _ _ (by have hu := lt_usize 32 (by decide); have hg := hm.gap; omega)
  unfold mintCallMem
  rw [callOutput32_size _ out ptr ho (by omega), hsz]

theorem mintCall_heap {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (out : ByteArray) (hb : ptr.toNat + 32 ≤ 2 ^ 200) (ho : out.size < UInt256.size) :
    HeapMemory (mintCallMem mem out ptr) (mintCallWords aw ptr) ptr := by
  have hh := selectorMem_heap hm mintWord hb
  have hsz : (selectorMem mem ptr mintWord).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size _ _ _ (by have hu := lt_usize 32 (by decide); have hg := hm.gap; omega)
  have hc := callOutput32_heap hh out ho (by omega)
  exact ⟨hc.size, hc.free, hc.lower, hc.gap,
    callActiveWords_active hh.active (by change ptr.toNat + 4 ≤ 2 ^ 200; omega) hb⟩

theorem mintCall_prefix {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (out : ByteArray) (ho : out.size < UInt256.size) :
    MemoryPrefix mem (mintCallMem mem out ptr) ptr.toNat := by
  have hsz : (selectorMem mem ptr mintWord).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size _ _ _ (by have hu := lt_usize 32 (by decide); have hg := hm.gap; omega)
  exact (selectorMem_prefix hm mintWord).trans
    (callOutput32_prefix _ out ptr ho (by omega))

theorem mintCallWords_mono {aw ptr} (ha : ActiveWords aw)
    (hb : ptr.toNat + 32 ≤ 2 ^ 200) : aw.toNat ≤ (mintCallWords aw ptr).toNat := by
  have h0 := expandedWords_mono (off := ptr) (size := ⟨32⟩) ha hb
  have h1 := callActiveWords_mono (outOff := ptr) (outSize := ⟨32⟩)
    (activeWords_expand32 ha hb)
    (show ptr.toNat + (⟨4⟩ : UInt256).toNat ≤ 2 ^ 200 by change ptr.toNat + 4 ≤ _; omega) hb
  exact le_trans h0 h1

theorem mintAfterFailure {I g s0 ret R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3071⟩ (⟨0⟩ :: ret :: R) mem aw out acc k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R) mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [dup1, iszero, push2 ⟨3111⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨3172⟩, jumpiNT (by decide)]⟩

end Auction
