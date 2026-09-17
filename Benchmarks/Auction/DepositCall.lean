import Benchmarks.Auction.DepositPrefix
import Benchmarks.Auction.RevertData
import Benchmarks.Auction.RawEthPrefix
import Benchmarks.Auction.BytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def depositCallWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords aw ptr ⟨32⟩) ptr ⟨4⟩

theorem depositCall_heap {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (selectorMem mem ptr depositWord) (depositCallWords aw ptr) ptr := by
  have hh := selectorMem_heap hm depositWord hb
  exact ⟨hh.size, hh.free, hh.lower, hh.gap,
    activeWords_expand hh.active (by change ptr.toNat + 4 ≤ 2 ^ 200; omega)⟩

theorem depositCall {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hyes : extCodeSizeWord σ (wethWord σ I) ≠ ⟨0⟩) (hov : R.length + 18 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) (Int.ofNat amount.toNat)
        depositSelector (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨3432⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨4⟩) :: amount :: ⟨0xd0e30db0⟩ ::
          wethWord σ I :: amount :: recipient :: ret :: R)
        (selectorMem mem ptr depositWord) (depositCallWords aw ptr) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd3431⟩ := depositCallPrefix h hm hb hyes hov
  have hcd : (selectorMem mem ptr depositWord).readWithPadding ptr.toNat 4 = depositSelector :=
    (selectorMem_read hm depositWord).trans depositWord_prefix
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd3432, ho⟩ :=
    callBridge rd3431 hs hperm (by native_decide) hcd (by decide) (by evm_ov)
  rw [callOutputMem_zero] at rd3432
  exact ⟨evm', cA', σ', z, out, _, _, hc, hs', rd3432, ho⟩

theorem depositAfterSuccess {I g s0 amount recipient ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨3432⟩
      (⟨1⟩ :: (ptr + ⟨4⟩) :: amount :: ⟨0xd0e30db0⟩ :: target ::
        amount :: recipient :: ret :: R) mem aw out acc k C)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3449⟩
      (amount :: ⟨0xd0e30db0⟩ :: target :: amount :: recipient :: ret :: R)
      mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [iszero, dup1, iszero, push2 ⟨3446⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, pop, pop]⟩

set_option synthInstance.maxSize 1024 in
theorem depositAfterFailure {I g s0 amount recipient ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨3432⟩
      (⟨0⟩ :: (ptr + ⟨4⟩) :: amount :: ⟨0xd0e30db0⟩ :: target ::
        amount :: recipient :: ret :: R) mem aw out acc k C)
    (hov : R.length + 12 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd3439 := evm_run h with [iszero, dup1, iszero, push2 ⟨3446⟩,
    jumpiNT (by decide)]
  exact rd3439.revertData (by unfold revertDataWf; native_decide) (by evm_ov)

end Auction
