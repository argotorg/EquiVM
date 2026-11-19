import Benchmarks.Midnight.FlashLoanEventEncode
import Benchmarks.Midnight.RuntimeBlocks_061

/-! The flash-loan log and the start of its outgoing transfer loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanEventLog {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw finish root callback tn tp an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 17 ≤ 1024)
    (hp : I.perm = true) (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨16253⟩
      ([finish, root, root, flashLoanEventTopic, UInt256.ofNat I.source.val, callback] ++
        flashLoanAfterEventStack tn tp callback an ap dl dp ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧ MemoryAccounting mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨16258⟩
        (UInt256.ofNat 0 :: (flashLoanAfterEventStack tn tp callback an ap dl dp ++ R))
        mem aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_16253
    (R := flashLoanAfterEventStack tn tp callback an ap dl dp ++ R)
    (by simp only [flashLoanAfterEventStack, List.length_append, List.length_cons,
      List.length_nil]; omega) hp rd
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  exact ⟨_, _, _, by omega, ha1, rd1⟩

theorem midnightFlashLoanEventStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hp : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨16253⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C) :
    RDstatic midnightBytecode g s0 := by
  have rd1 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2 := rd1.sub (by native_decide) (by evm_ov)
  have rd3 := rd2.swap1 (by native_decide) (by evm_ov)
  exact rd3.log3Static hp (by native_decide) (by omega)

end Benchmarks.Midnight
