import Solm.Benchmarks.Auction.BidStorage
import Solm.Benchmarks.Auction.Log2

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem bidEvent {I g s0 extended bidder snap noun ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1792⟩ (extended :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata acc k C)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ mem' aw' k' C', RD auctionBytecode I g s0 ⟨1859⟩
      (extended :: bidder :: snap :: noun :: ret :: R) mem' aw' rdata acc k' C' := by
  have rd1802 := evm_run h with [jumpdest, dup3,
    raw mloadSymbolic (by native_decide) (by evm_ov), push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov), caller, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd1817 := evm_run rd1802 with [callvalue, push1 ⟨32⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), dup4, iszero, iszero, dup2, dup4, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), swap1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have rd1850 := rd1817.pushConst
    ⟨0x1159164c56f277e6fc99c11731bd380e0347deb969b75523398734c252706ea3⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858 := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  obtain ⟨_, _, hr⟩ := rd1858.log2Symbolic (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, _, _, hr⟩

theorem bidExtendedEvent {I g s0 extended bidder snap noun ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1865⟩ (extended :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata acc k C)
    (hperm : I.perm = true) (hov : R.length + 11 ≤ 1024) :
    ∃ mem' aw' k' C', RD auctionBytecode I g s0 ⟨1923⟩
      (extended :: bidder :: snap :: noun :: ret :: R) mem' aw' rdata acc k' C' := by
  have rd1878 := evm_run h with [dup3, raw mloadSymbolic (by native_decide) (by evm_ov),
    push1 ⟨96⟩, dup5, add, raw mloadSymbolic (by native_decide) (by evm_ov), push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov), swap1, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd1911 := rd1878.pushConst
    ⟨0x6e912a3a9105bdd2af817ba5adc14e6c127c1035b5b648faa29ca0d58ab8ff4e⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1911 with [swap1, push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov), dup1, swap2, sub, swap1]
  obtain ⟨_, _, hr⟩ := rd1922.log2Symbolic (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, _, _, hr⟩

theorem bidEvents {I g s0 extended bidder snap noun ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1792⟩ (extended :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata acc k C)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ mem' aw' k' C', RD auctionBytecode I g s0 ⟨1923⟩
      (extended :: bidder :: snap :: noun :: ret :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨_, _, _, _, rd1859⟩ := bidEvent h hperm hov
  have rd1864 := evm_run rd1859 with [dup1, iszero, push2 ⟨1923⟩]
  by_cases hz : extended = ⟨0⟩
  · exact ⟨_, _, _, _, evm_run rd1864 with [jumpiT (by rw [hz]; decide) (by jump_dest)]⟩
  · have rd1865 := evm_run rd1864 with [jumpiNT (isZero_eq_zero_of_ne hz)]
    exact bidExtendedEvent rd1865 hperm (by omega)

end Auction
