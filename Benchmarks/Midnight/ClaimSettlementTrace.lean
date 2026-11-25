import Benchmarks.Midnight.ClaimSettlementSource
import Benchmarks.Midnight.CheckedArithmetic
import Benchmarks.Midnight.SafeTransfer
import Benchmarks.Midnight.ScratchMemory

variable {fork : Ethereum.Fork}

/-! Settlement-claim bytecode from authorization through the token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def claimSettlementMemory (token : AccountAddress) (amount : UInt256) : ByteArray :=
  writeWord (mappingMemory (UInt256.ofNat token.val) ⟨6⟩) 832 amount

theorem claimSettlementMemory_properties (token : AccountAddress) (amount : UInt256) :
    (claimSettlementMemory token amount).size = 864 ∧
    memLoad (UInt256.ofNat 64) (claimSettlementMemory token amount) = ⟨832⟩ ∧
    memLoad (UInt256.ofNat 96) (claimSettlementMemory token amount) = ⟨0⟩ := by
  have hzero : memLoad (UInt256.ofNat 96) midnightEntryMemory = ⟨0⟩ := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · rw [claimSettlementMemory, writeWord_sparse_size, mappingMemory_size]
    rfl
  · rw [claimSettlementMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [mappingMemory_size]; decide) (Or.inl (by decide)), mappingMemory_freePtr]
  · rw [claimSettlementMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [mappingMemory_size]; decide) (Or.inl (by decide)), mappingMemory,
      memLoad_twoWordHashMem _ _ _ (by decide) (by rw [midnightEntryMemory_size]; decide), hzero]

theorem claimSettlementTraceSubtract {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token receiver : AccountAddress} {amount : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨17693⟩
      (UInt256.ofNat receiver.val :: amount :: UInt256.ofNat token.val :: R)
      midnightEntryMemory aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨19447⟩
      (solcSlotWordAt (claimSettlementSlot token) σ I :: amount :: ⟨17729⟩ ::
        claimSettlementSlot token :: UInt256.ofNat token.val :: UInt256.ofNat token.val ::
        UInt256.ofNat receiver.val :: amount :: ⟨15786⟩ :: R)
      (mappingMemory (UInt256.ofNat token.val) ⟨6⟩) aw' rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_17693 hstack (by jump_dest) rd
  have hclean : UInt256.land (UInt256.ofNat token.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      UInt256.ofNat token.val := addressMaskLiteral_clean_of_canonical (addressWord_canonical token)
  simp only [midnightBlocks.midnight_block_17693_stack,
    midnightBlocks.midnight_block_17693_memory, hclean] at rd1
  have hmem : (UInt256.ofNat 6).toByteArray.write 0
      ((UInt256.ofNat token.val).toByteArray.write 0 midnightEntryMemory
        (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32 =
      mappingMemory (UInt256.ofNat token.val) ⟨6⟩ := rfl
  rw [hmem, mappingMemory_hash] at rd1
  exact ⟨_, _, _, rd1⟩

theorem claimSettlementTraceStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token receiver : AccountAddress} {amount balance : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g s0 ⟨17729⟩
      (UInt256.sub balance amount :: claimSettlementSlot token :: UInt256.ofNat token.val ::
        UInt256.ofNat token.val :: UInt256.ofNat receiver.val :: amount :: ⟨15786⟩ :: R)
      (mappingMemory (UInt256.ofNat token.val) ⟨6⟩) aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨23236⟩
      (UInt256.ofNat token.val :: UInt256.ofNat receiver.val :: amount :: ⟨15786⟩ :: R)
      (claimSettlementMemory token amount) aw' rdata
      (sstoreAccountMap I.codeOwner σ (claimSettlementSlot token) (UInt256.sub balance amount))
      k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_17729_packed
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd
  simpa only [midnightBlocks.midnight_block_17729_stack,
    midnightBlocks.midnight_block_17729_memory, mappingMemory_freePtr] using
      (show ∃ aw' k' C', RD fork _ _ _ _ _ _ _ aw' _ _ k' C' from ⟨aw1, k1, C1, rd1⟩)

theorem claimSettlementTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value slot : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨17729⟩ (value :: slot :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  have rd1 := rd.jumpdest (by native_decide) hstack
  have rd2 := rd1.swap1 (by native_decide) (by simp; omega)
  exact rd2.sstoreStatic hperm (by native_decide) (by omega)

end Benchmarks.Midnight
