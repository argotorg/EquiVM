import Benchmarks.Midnight.RepayWithdrawableWrite
import Benchmarks.Midnight.TransferBudget

/-! Repay event memory and the branch to its optional callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def repayEventMemory (mem : ByteArray) (root units : UInt256) (payer : AccountAddress) : ByteArray :=
  writeWordArray mem root.toNat [units, UInt256.ofNat payer.val]

def repayAfterEventPC (callback : AccountAddress) : UInt256 :=
  if callback = 0 then ⟨10100⟩ else ⟨10127⟩

theorem midnightRepayEvent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id dp dl user units market : UInt256}
    {callback payer : AccountAddress} {σ : AccountMap} {credit k C : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hperm : I.perm = true)
    (hroot : root.toNat < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10034⟩
      ([repayHasCallback callback, id, dp, UInt256.ofNat callback.val, dl, user,
        UInt256.ofNat payer.val, units, market] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit (repayEventMemory mem root units payer) aw' C' ∧
      RD midnightBytecode I g s0 (repayAfterEventPC callback)
        ([id, dp, UInt256.ofNat callback.val, dl, user, UInt256.ofNat payer.val, units, market] ++ R)
        (repayEventMemory mem root units payer) aw' rdata σ k' C' := by
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hm : midnightBlocks.midnight_block_10034_taken_memory (mem := mem)
      (x6 := UInt256.ofNat payer.val) (x7 := units) = repayEventMemory mem root units payer := by
    simp only [midnightBlocks.midnight_block_10034_taken_memory, hfree, h32,
      addressMask_computed, solcAddrMask_clean (addressWord_canonical payer),
      repayEventMemory, writeWordArray, Reasoning.Theory.writeWord, Nat.add_zero]
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hz : callback = 0
  · have rd1 := midnightBlocks.midnight_block_10034_fallthrough
      (by simp only [List.length_cons]; omega) hperm
      (by simp only [repayHasCallback, hz, if_true]; rfl) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_10034_fallthrough_memory
      transfer_budget hb)
    change midnightBlocks.midnight_block_10034_fallthrough_memory (mem := mem)
      (x6 := UInt256.ofNat payer.val) (x7 := units) = _ at hm
    rw [hm] at rd1 hb1
    exact ⟨_, _, _, hb1, by simpa only [repayAfterEventPC, hz, if_true,
      midnightBlocks.midnight_block_10034_fallthrough_stack] using rd1⟩
  · have rd1 := midnightBlocks.midnight_block_10034_taken
      (by simp only [List.length_cons]; omega) hperm
      (by simp only [repayHasCallback, hz, if_false]; decide) (by jump_dest) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_10034_taken_memory
      transfer_budget hb)
    rw [hm] at rd1 hb1
    exact ⟨_, _, _, hb1, by simpa only [repayAfterEventPC, hz, if_false,
      midnightBlocks.midnight_block_10034_taken_stack] using rd1⟩

end Benchmarks.Midnight
