import Benchmarks.EAS.Attester.MultiAttestSourceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem multiAttestRowsEnd_eq_allocation (cd : ByteArray) (free : Nat) (secondData : UInt256)
    (i remaining : Nat) :
    multiAttestRowsEnd cd free secondData i remaining =
      attestAllocationEnd (free + 96 * remaining)
        (fun j ↦ (rowLength cd secondData j).toNat) i remaining := by
  induction remaining generalizing free i with
  | zero => simp only [multiAttestRowsEnd, attestAllocationEnd, Nat.mul_zero, Nat.add_zero]
  | succ remaining ih =>
      rw [multiAttestRowsEnd, ih, attestAllocationEnd]
      rw [show free + 96 + 480 * (rowLength cd secondData i).toNat + 96 * remaining =
        free + 96 * (remaining + 1) + 480 * (rowLength cd secondData i).toNat by omega]

theorem multiAttestBuiltFree_eq_allocation (cd : ByteArray) :
    multiAttestBuiltFree cd =
      attestAllocationEnd (160 + 192 * arrayCount cd 4) (multiAttestCounts cd) 0 (arrayCount cd 4)
          := by
  rw [multiAttestBuiltFree, multiAttestRowsEnd_eq_allocation]
  rw [show 160 + 96 * arrayCount cd 4 + 96 * arrayCount cd 4 =
    160 + 192 * arrayCount cd 4 by omega]
  rfl

end Benchmarks.EAS.Attester
