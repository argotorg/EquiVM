import Benchmarks.Auction.CallOutput

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem expandedWords_mono {aw off size : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + size.toNat ≤ 2 ^ 200) : aw.toNat ≤ (expandedWords aw off size).toNat := by
  have hm := memoryWords_bounds aw.toNat off.toNat size.toNat ha.2 hb
  change aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat size.toNat)).toNat
  rw [ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
  exact hm.1

theorem callActiveWords_mono {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    aw.toNat ≤ (callActiveWords aw inOff inSize outOff outSize).toNat := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  rw [callActiveWords_toNat ha hi ho]
  exact le_trans hm1.1 hm2.1

theorem expandedWords32_eq_of_cover {aw off : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + 32 ≤ 2 ^ 200) (hc : off.toNat + 32 ≤ aw.toNat * 32) :
    expandedWords aw off ⟨32⟩ = aw := by
  apply u256_inj
  rw [expandedWords32_toNat ha hb]
  exact max_eq_left (by omega)

theorem expandedWords32_chain {aw off1 off2 : UInt256} (ha : ActiveWords aw)
    (hle : off1.toNat ≤ off2.toNat) (hb : off2.toNat + 32 ≤ 2 ^ 200) :
    expandedWords (expandedWords aw off1 ⟨32⟩) off2 ⟨32⟩ = expandedWords aw off2 ⟨32⟩ := by
  apply u256_inj
  have hb1 : off1.toNat + 32 ≤ 2 ^ 200 := by omega
  rw [expandedWords32_toNat (activeWords_expand32 ha hb1) hb,
    expandedWords32_toNat ha hb1, expandedWords32_toNat ha hb]
  omega

theorem HeapMemory.expand32 {mem aw ptr} (hm : HeapMemory mem aw ptr) (off : UInt256)
    (hb : off.toNat + 32 ≤ 2 ^ 200) : HeapMemory mem (expandedWords aw off ⟨32⟩) ptr :=
  ⟨hm.size, hm.free, hm.lower, hm.gap, activeWords_expand32 hm.active hb⟩

end Auction
