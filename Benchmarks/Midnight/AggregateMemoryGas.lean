import Benchmarks.Midnight.CallForwardingGas
import Benchmarks.Midnight.TransferGas

/-! Aggregate parent/child memory capacity with a linear parent-work margin. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem aggregateMemoryWords_bound {parent child gas : Nat}
    (hpaid : memoryCost parent + 4 * parent + forwardingMinimum (memoryCost child) ≤
      gas + 1000000)
    (hgas : gas < 327073817860464196263953616796569) :
    parent + child < 2^59 - 1 := by
  by_contra hlarge
  have hsum : 576460752303423487 ≤ parent + child := by omega
  have hsum2 := Nat.mul_le_mul hsum hsum
  have hp : parent * parent ≤ 512 * (parent * parent / 512) + 511 := by omega
  have hc : child * child ≤ 512 * (child * child / 512) + 511 := by omega
  have hf : 64 * memoryCost child ≤ 63 * forwardingMinimum (memoryCost child) + 63 := by
    unfold forwardingMinimum
    omega
  have hpoly : 63 * parent * parent + 64 * child * child +
      225792 * parent + 98304 * child ≤ 32256 * (gas + 1000000) + 97153 := by
    unfold memoryCost at hpaid hf
    simp only [Nat.mul_assoc]
    omega
  have hthreshold :
      127 * (32256 * (327073817860464196263953616796568 + 1000000) + 97153) +
        4063297536 <
      4032 * 576460752303423487 ^ 2 + 20643840 * 576460752303423487 := by
    decide +kernel
  zify at hsum hsum2 hpoly hgas hthreshold
  nlinarith [sq_nonneg (63 * (parent : Int) - 64 * (child : Int) + 63744)]

theorem aggregateReturnDataFits {ptr : UInt256} {size parent spent gas : Nat}
    (hptr : ptr.toNat ≤ 32 * parent)
    (hpaid : memoryCost parent + 4 * parent ≤ spent + 1000000)
    (hgas : gas < 327073817860464196263953616796569)
    (hchild : spent + forwardingMinimum (memoryCost ((size + 31) / 32)) ≤ gas) :
    ptr.toNat + returnDataAllocation size < 2^64 := by
  have hb := aggregateMemoryWords_bound (parent := parent) (child := (size + 31) / 32)
    (gas := gas) (by omega) hgas
  unfold returnDataAllocation
  omega

end Benchmarks.Midnight
