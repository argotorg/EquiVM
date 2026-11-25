import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_20895_taken`. -/
def midnight_block_20895_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad x0 mem) + x1) mem) :: R)

/-- Final memory for bytecode block summary `midnight_block_20895_taken`. -/
def midnight_block_20895_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20895. -/
theorem midnight_block_20895_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21100) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20895) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21100) (midnight_block_20895_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20895_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + x1) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
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
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21100) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21100)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20895_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21100) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20895) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21100) (midnight_block_20895_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20895_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_20895_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20895_fallthrough`. -/
def midnight_block_20895_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad x0 mem) + x1) mem) :: R)

/-- Final memory for bytecode block summary `midnight_block_20895_fallthrough`. -/
def midnight_block_20895_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20895. -/
theorem midnight_block_20895_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20895) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20920) (midnight_block_20895_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20895_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + x1) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
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
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21100) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20920)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20895_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 7).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20895) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20920) (midnight_block_20895_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20895_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_20895_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20920`. -/
def midnight_block_20920_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x4 mem) :: x6 :: (UInt256.ofNat 20932) :: (UInt256.ofNat 64) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20920. -/
theorem midnight_block_20920 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20920_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M aw x4 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 20932) (by native_decide) (by evm_ov)
  have r3 := r2.dup9 (by native_decide) (by evm_ov)
  have r4 := r3.dup8 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19460) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19460)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20920_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20920_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20920 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20932_taken`. -/
def midnight_block_20932_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad x0 mem) + x1) mem) :: R)

/-- Final memory for bytecode block summary `midnight_block_20932_taken`. -/
def midnight_block_20932_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20932. -/
theorem midnight_block_20932_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21085) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21085) (midnight_block_20932_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20932_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + x1) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
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
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21085) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21085)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20932_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21085) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21085) (midnight_block_20932_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20932_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_20932_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20932_fallthrough`. -/
def midnight_block_20932_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad x0 mem) + x1) mem) :: R)

/-- Final memory for bytecode block summary `midnight_block_20932_fallthrough`. -/
def midnight_block_20932_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20932. -/
theorem midnight_block_20932_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20957) (midnight_block_20932_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20932_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + x1) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
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
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 21085) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20957)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20932_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((memLoad ((memLoad x0 mem) + x1) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20957) (midnight_block_20932_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20932_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_20932_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20957`. -/
def midnight_block_20957_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 20966) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20957. -/
theorem midnight_block_20957 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24250) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20957) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24250) (midnight_block_20957_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 20966) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 24250) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24250)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20957_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24250) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20957) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24250) (midnight_block_20957_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20957 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20966. -/
theorem midnight_block_20966_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 2000000000000000000)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21070) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20966) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21070) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 2000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 21070) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21070)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20966_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 2000000000000000000)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21070) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20966) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21070) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20966_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20966. -/
theorem midnight_block_20966_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 2000000000000000000)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20966) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 2000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 21070) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20982)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20966_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 2000000000000000000)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20966) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20966_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20982_taken`. -/
def midnight_block_20982_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.eq x1 (UInt256.ofNat 1000000000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20982. -/
theorem midnight_block_20982_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 (UInt256.ofNat 1000000000000000000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21033) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21033) (midnight_block_20982_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 21033) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21033)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20982_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 (UInt256.ofNat 1000000000000000000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21033) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21033) (midnight_block_20982_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20982_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20982_fallthrough`. -/
def midnight_block_20982_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.eq x1 (UInt256.ofNat 1000000000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20982. -/
theorem midnight_block_20982_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 (UInt256.ofNat 1000000000000000000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (midnight_block_20982_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 21033) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21000)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20982_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq x1 (UInt256.ofNat 1000000000000000000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20982) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (midnight_block_20982_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20982_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21000_taken`. -/
def midnight_block_21000_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 21000. -/
theorem midnight_block_21000_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21018) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21018) (midnight_block_21000_taken_stack (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 21018) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21018)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21000_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21018) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21018) (midnight_block_21000_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21000_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21000_fallthrough`. -/
def midnight_block_21000_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 21000. -/
theorem midnight_block_21000_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21008) (midnight_block_21000_fallthrough_stack (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 21018) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21008)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21000_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21008) (midnight_block_21000_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21000_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21008`. -/
def midnight_block_21008_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: x4 :: (x5 + (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21008. -/
theorem midnight_block_21008 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20840) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21008) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (midnight_block_21008_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap6 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20840) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20840)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21008_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20840) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21008) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (midnight_block_21008_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21008 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 21018. -/
theorem midnight_block_21018 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21018) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 582370619) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `midnight_block_21033`. -/
def midnight_block_21033_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.ofNat 21061) :: (UInt256.ofNat 999000000000000000000000000000000000) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21033. -/
theorem midnight_block_21033 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21033) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_21033_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 999000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21061) (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20413)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21033_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21033) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_21033_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21033 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21061`. -/
def midnight_block_21061_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (UInt256.isZero (UInt256.gt x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21061. -/
theorem midnight_block_21061 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21000) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21061) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (midnight_block_21061_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.gt (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21000) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21000)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21061_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21000) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21061) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21000) (midnight_block_21061_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21061 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 21070. -/
theorem midnight_block_21070 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21070) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3100483357) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21085. -/
theorem midnight_block_21085 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21085) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 793384515) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21100. -/
theorem midnight_block_21100 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21100) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 25636351) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 230) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21115. -/
theorem midnight_block_21115 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21115) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3061052203) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

end midnightBlocks
