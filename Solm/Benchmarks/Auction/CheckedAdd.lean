import Solm.Benchmarks.Auction.DynamicMemory
import EVMReasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem arithmeticPanic {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5630⟩ R mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) : RDrev auctionBytecode g s0 := by
  exact evm_run h with [jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨36⟩, push0,
    raw revertSymbolic (by native_decide) (by evm_ov)]

theorem arithmeticReturn {I g s0 value a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4886⟩ (value :: a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (value :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

theorem checkedAddOk {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5704⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hno : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret ((b + a) :: R) mem aw rdata acc k' C' := by
  have hlt : UInt256.gt a (b + a) = ⟨0⟩ :=
    constructorCheckedAddNoOverflowLt a b (by omega)
  have rd4886 := evm_run h with [jumpdest, dup1, dup3, add, dup1, dup3, gt,
    iszero, push2 ⟨4886⟩, jumpiT (by rw [hlt]; decide) (by jump_dest)]
  exact arithmeticReturn rd4886 hret (by evm_ov)

theorem checkedAddOverflow {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5704⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hlt : UInt256.gt a (b + a) = ⟨1⟩ := constructorCheckedAddOverflowLt a b hover
  have rd5716 := evm_run h with [jumpdest, dup1, dup3, add, dup1, dup3, gt,
    iszero, push2 ⟨4886⟩, jumpiNT (by rw [hlt]; decide)]
  have rd5630 := evm_run rd5716 with [push2 ⟨4886⟩, push2 ⟨5630⟩, jump (by jump_dest)]
  exact arithmeticPanic rd5630 (by evm_ov)

end Auction
