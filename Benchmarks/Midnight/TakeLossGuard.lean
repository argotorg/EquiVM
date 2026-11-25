import Benchmarks.Midnight.TakeAuthorizationRead
import Benchmarks.Midnight.RuntimeBlocks_042
import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.LiquidatePositionMemory

variable {fork : Ethereum.Fork}

/-! Save the market id and reject a saturated loss factor before evaluating an offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeMarketMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  twoWordHashMem id (UInt256.ofNat 1) (writeWord mem 512 id)

set_option maxHeartbeats 800000 in
theorem midnightTakeLossGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id ratifierPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10969⟩ (id :: ratifierPtr :: R) mem aw rdata σ k C) :
    ((¬ (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I)
        (UInt256.ofNat 128)).toNat < 2^128 - 1) ∧ RDrev fork midnightBytecode g s0) ∨
    ((UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I)
        (UInt256.ofNat 128)).toNat < 2^128 - 1 ∧
      ∃ aw' k' C', MemoryFunding credit (takeMarketMemory mem id) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11009⟩ (ratifierPtr :: solcMappingSlot ⟨1⟩ id :: R)
          (takeMarketMemory mem id) aw' rdata σ k' C') := by
  have hstore : memLoad (UInt256.ofNat 512)
      (id.toByteArray.write 0 mem (UInt256.ofNat 512).toNat 32) = id :=
    memLoad_writeWord mem (UInt256.ofNat 512) id
  have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 1) (writeWord mem 512 id)) =
      solcMappingSlot ⟨1⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by rw [writeWord_sparse_size]; omega)
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have ha13 := memoryFundingAt (credit := credit) r13 (by memory_fund ha)
  simp only [hstore, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r13 ha13
  simp only [show (UInt256.ofNat 512).toNat = 512 from rfl, writeWord_fold] at r13 ha13
  rw [hhash] at r13
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have ha20 := memoryFundingAt (credit := credit) r20 (by memory_fund ha13)
  obtain ⟨_, _, hc21, r21⟩ := RD.sloadMono r20 (by native_decide) (by evm_ov)
  have ha21 := ha20.mono hc21
  have r22 := r21.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r23 := r22.shr (by native_decide) (by evm_ov)
  have r24 := r23.lt (by native_decide) (by evm_ov)
  have r25 := r24.iszero (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 14998) (by native_decide) (by evm_ov)
  simp only [uint128Mask_computed] at r26
  by_cases hg : (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I)
      (UInt256.ofNat 128)).toNat < 2^128 - 1
  · have hc : UInt256.lt (UInt256.shiftRight
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)) uint128Mask = ⟨1⟩ :=
      ult_one hg
    have r27 := r26.jumpiNT (by native_decide) (by
      change UInt256.isZero (UInt256.lt (UInt256.shiftRight
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)) uint128Mask) = ⟨0⟩
      rw [hc]; rfl) (by evm_ov)
    have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11009)) r27 (by native_decide)
    have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund ha21)
    exact Or.inr ⟨hg, _, _, _, haFinal, rFinal⟩
  · have hc : UInt256.lt (UInt256.shiftRight
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)) uint128Mask = ⟨0⟩ :=
      ult_zero (by change 2^128 - 1 ≤ _; omega)
    have r27 := r26.jumpiT (by native_decide) (by
      change UInt256.isZero (UInt256.lt (UInt256.shiftRight
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)) uint128Mask) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) (by evm_ov)
    exact Or.inl ⟨hg, midnightBlocks.midnight_block_14998 (by
      simp only [List.length_cons]; omega) r27⟩

end Benchmarks.Midnight
