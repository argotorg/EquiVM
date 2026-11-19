import Benchmarks.Midnight.PrecompileOutput
import Benchmarks.Midnight.ReturnData
import Benchmarks.Midnight.Conditions

/-! Capacity of a transfer's return-data allocation when its input heap is small. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem returnDataAllocation_lt_of_memoryCost {size gas words : Nat}
    (hcost : memoryCost ((size + 31) / 32) ≤ gas)
    (hgas : gas < memoryCost words) :
    returnDataAllocation size < (words + 1) * 32 := by
  have hn : (size + 31) / 32 < words := by
    by_contra h
    have hm := memoryCost_mono (show words ≤ (size + 31) / 32 by omega)
    omega
  unfold returnDataAllocation
  omega

theorem transferReturnDataAllocation_bound {size : Nat} {g : UInt256}
    (hgas : midnightGasBound g)
    (hout : size ≤ 1024 ∨ memoryCost ((size + 31) / 32) ≤ g.toNat) :
    returnDataAllocation size < 3 * 2 ^ 62 := by
  rcases hout with hsmall | hcost
  · unfold returnDataAllocation
    omega
  · have hb : 327073817860464196263953616796569 ≤ memoryCost (3 * 2 ^ 57 - 1) :=
      by decide +kernel
    have hlt : g.toNat < memoryCost (3 * 2 ^ 57 - 1) :=
      (midnightGasBound_lt_capacityCutoff hgas).trans_le hb
    have h := returnDataAllocation_lt_of_memoryCost hcost hlt
    norm_num at h ⊢
    exact h

theorem transferReturnDataFits {ptr : UInt256} {size : Nat} {g : UInt256}
    (hptr : ptr.toNat ≤ 2 ^ 62) (hgas : midnightGasBound g)
    (hout : size ≤ 1024 ∨ memoryCost ((size + 31) / 32) ≤ g.toNat) :
    ptr.toNat + returnDataAllocation size < 2 ^ 64 := by
  have hb := transferReturnDataAllocation_bound hgas hout
  omega

end Benchmarks.Midnight
