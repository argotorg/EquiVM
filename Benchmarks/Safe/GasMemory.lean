import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: expanding to a huge byte range cannot be paid with word-sized gas.
theorem memExpansionCost_huge (aw off len : UInt256)
    (hpaid : Cₘ aw < UInt256.size) (hlen : 2 ^ 138 ≤ len.toNat) :
    UInt256.size ≤ memExpansionCost aw off len := by
  have hbound := MachineState.M_lt_uint256_size aw.val.isLt off.val.isLt len.val.isLt
  have hwords : 2 ^ 133 ≤ MachineState.M aw.toNat off.toNat len.toNat := by
    unfold MachineState.M
    split
    · rename_i hz
      norm_num [hz] at hlen
    · apply le_trans _ (le_max_right _ _)
      omega
  have hcost := Cₘ_monotone_of_lt hwords hbound
  have hlarge : 2 * UInt256.size ≤ Cₘ (UInt256.ofNat (2 ^ 133)) := by decide
  change UInt256.size ≤
    Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) - Cₘ aw
  omega

end Benchmarks.Safe
