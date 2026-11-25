import Benchmarks.Midnight.RuntimeBlocks_080
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.StorageWriteGas

variable {fork : Ethereum.Fork}

/-! Funding through the collateral configuration reads. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks
set_option maxRecDepth 10000

-- GENERALIZES the storage-read block with retained memory funding.
theorem midnight_block_20895_fallthrough_funded {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    {credit : Nat} (hfund : MemoryFunding credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20895) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), MemoryFunding credit (midnight_block_20895_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20920) (midnight_block_20895_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20895_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc15, r15⟩ := RD.sloadMono r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21100) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20920)) r19 (by native_decide)
  simp only [memExpansionCost] at hc15
  exact ⟨_, _, _, by
    unfold midnight_block_20895_fallthrough_memory
    memory_fund hfund, rFinal⟩

-- GENERALIZES the storage-read block with retained memory funding.
theorem midnight_block_20932_fallthrough_funded {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    {credit : Nat} (hfund : MemoryFunding credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), MemoryFunding credit (midnight_block_20932_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20957) (midnight_block_20932_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20932_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc15, r15⟩ := RD.sloadMono r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21085) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20957)) r19 (by native_decide)
  simp only [memExpansionCost] at hc15
  exact ⟨_, _, _, by
    unfold midnight_block_20932_fallthrough_memory
    memory_fund hfund, rFinal⟩

end Benchmarks.Midnight
