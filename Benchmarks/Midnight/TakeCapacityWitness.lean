import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.CallForwardingGas
import Benchmarks.Midnight.TransferGas

/-! Exact arithmetic for the cheaper token identified by `TakeCapacityAudit.lean`.

These certificates check the numerical witness, not a parameterized execution of `take`.
The targeted EVM measurements establish the ordinary-size instances of the parent-cost
formula. The token `42 5f 52 59 35 5f f3` uses fourteen non-memory gas: after storing
TIMESTAMP = 1, MSIZE = 32 selects CALLDATALOAD(32). With the payer divisible by 2^32,
that word is the transfer recipient divided by 2^32.
-/

open Ethereum Ethereum.EVM

namespace Benchmarks.Midnight.TakeCapacityWitness

def parentWords : Nat := 290499906672590983
def replyWords : Nat := 285960845630832504
def startingGas : Nat := 327073817860464196263953616796567
def selfAddress : Nat := 64 * 2^32
def payer : Nat := 0x3000 * 2^32
def receiver : Nat := 32 * replyWords * 2^32

theorem gas_formula :
    memoryCost parentWords + 3 * parentWords + 26766 +
      forwardingMinimum (memoryCost replyWords + 14) = startingGas := by
  decide +kernel

theorem gas_below_former_cutoff : startingGas < 327073817860464196263953616796569 := by
  decide +kernel

theorem gas_excluded : ¬ midnightGasBound (UInt256.ofNat startingGas) := by
  unfold midnightGasBound
  decide +kernel

theorem below_cutoff_by_two :
    startingGas + 2 = 327073817860464196263953616796569 := by
  decide +kernel

theorem address_bounds :
    selfAddress < 2^160 ∧ payer < 2^160 ∧ receiver < 2^160 := by
  decide +kernel

theorem reply_selection :
    payer % 2^32 = 0 ∧ selfAddress / 2^32 = 64 ∧ receiver / 2^32 = 32 * replyWords := by
  decide +kernel

theorem input_length :
    32 * (parentWords - 127) = 9295997013522907392 ∧
      1696 + 32 * (parentWords - 127) < 2^64 := by
  decide +kernel

theorem allocation_hits_limit :
    32 * parentWords + returnDataAllocation (32 * replyWords) = 2^64 := by
  decide +kernel

theorem allocator_rejects :
    allocationCheck (UInt256.ofNat (32 * parentWords)) (UInt256.ofNat (2^64)) ≠ ⟨0⟩ := by
  exact allocationCheck_large (by decide +kernel) (by decide +kernel)

theorem forwarding_suffices :
    memoryCost replyWords + 14 ≤ L (forwardingMinimum (memoryCost replyWords + 14)) := by
  decide +kernel

theorem retained_parent_gas :
    forwardingMinimum (memoryCost replyWords + 14) - (memoryCost replyWords + 14) =
      2535144011467672880345371312674 := by
  decide +kernel

end Benchmarks.Midnight.TakeCapacityWitness
