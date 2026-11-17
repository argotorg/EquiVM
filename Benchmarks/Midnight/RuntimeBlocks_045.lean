import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final memory for bytecode block summary `midnight_block_11681_taken`. -/
def midnight_block_11681_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11681. -/
theorem midnight_block_11681_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14604) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14604) R (midnight_block_11681_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shl (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 14604) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14604)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11681_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14604) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14604) R (midnight_block_11681_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11681_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11681_fallthrough`. -/
def midnight_block_11681_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11681. -/
theorem midnight_block_11681_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R (midnight_block_11681_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shl (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 14604) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11710)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11681_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 416) + (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32))) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R (midnight_block_11681_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11681_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11710_taken`. -/
def midnight_block_11710_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: (UInt256.ofNat 11794) :: R)

/-- Final memory for bytecode block summary `midnight_block_11710_taken`. -/
def midnight_block_11710_taken_memory {mem : ByteArray} : ByteArray :=
  ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11710. -/
theorem midnight_block_11710_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14594) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14594) (midnight_block_11710_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11710_taken_memory (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 11794) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r38 := r37.push0 (by native_decide) (by evm_ov)
  have r39 := RD.genKeccak256 r38 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r40⟩ := RD.sload r39 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r43 := r42.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r44 := RD.genMload r43 (by native_decide) (by evm_ov)
  have r45 := r44.add (by native_decide) (by evm_ov)
  have r46 := RD.genMload r45 (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push0 (by native_decide) (by evm_ov)
  have r50 := r49.eq (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 14594) (by native_decide) (by evm_ov)
  have r52 := r51.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14594)) r52 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11710_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14594) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14594) (midnight_block_11710_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11710_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_11710_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11710_fallthrough`. -/
def midnight_block_11710_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: (UInt256.ofNat 11794) :: R)

/-- Final memory for bytecode block summary `midnight_block_11710_fallthrough`. -/
def midnight_block_11710_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11710. -/
theorem midnight_block_11710_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11785) (midnight_block_11710_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11710_fallthrough_memory (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 11794) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r38 := r37.push0 (by native_decide) (by evm_ov)
  have r39 := RD.genKeccak256 r38 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r40⟩ := RD.sload r39 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r43 := r42.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r44 := RD.genMload r43 (by native_decide) (by evm_ov)
  have r45 := r44.add (by native_decide) (by evm_ov)
  have r46 := RD.genMload r45 (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push0 (by native_decide) (by evm_ov)
  have r50 := r49.eq (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 14594) (by native_decide) (by evm_ov)
  have r52 := r51.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11785)) r52 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11710_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 384) mem)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11710) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11785) (midnight_block_11710_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11710_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_11710_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11785`. -/
def midnight_block_11785_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 256) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11785. -/
theorem midnight_block_11785 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11785) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_11785_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11785_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11785) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_11785_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11785 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11794_taken`. -/
def midnight_block_11794_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11794_taken`. -/
def midnight_block_11794_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11794. -/
theorem midnight_block_11794_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 480) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14579) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11794) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14579) (midnight_block_11794_taken_stack (R := R)) (midnight_block_11794_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 14579) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14579)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11794_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 480) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14579) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11794) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14579) (midnight_block_11794_taken_stack (R := R)) (midnight_block_11794_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11794_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11794_fallthrough`. -/
def midnight_block_11794_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11794_fallthrough`. -/
def midnight_block_11794_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11794. -/
theorem midnight_block_11794_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 480) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11794) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) (midnight_block_11794_fallthrough_stack (R := R)) (midnight_block_11794_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 14579) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11826)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11794_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (UInt256.ofNat 480) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) + (UInt256.ofNat 416)) (x0.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11794) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) (midnight_block_11794_fallthrough_stack (R := R)) (midnight_block_11794_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11794_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11826_taken`. -/
def midnight_block_11826_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32) (UInt256.ofNat 448).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11826. -/
theorem midnight_block_11826_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14545) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14545) R (midnight_block_11826_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((52) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 14545) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14545)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11826_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14545) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14545) R (midnight_block_11826_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11826_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11826_fallthrough`. -/
def midnight_block_11826_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32) (UInt256.ofNat 448).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11826. -/
theorem midnight_block_11826_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11851) R (midnight_block_11826_fallthrough_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((52) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 14545) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11851)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11826_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11826) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11851) R (midnight_block_11826_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11826_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11851`. -/
def midnight_block_11851_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 544) ((UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32) (UInt256.ofNat 448).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11851. -/
theorem midnight_block_11851 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11851) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11880) R (midnight_block_11851_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((51) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 544) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11880)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11851_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11851) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11880) R (midnight_block_11851_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11851 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11880`. -/
def midnight_block_11880_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 14521) :: (UInt256.isZero (UInt256.isZero (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))))) :: (UInt256.isZero (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 448) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: x0 :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_11880`. -/
def midnight_block_11880_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 448) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 576) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11880. -/
theorem midnight_block_11880 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11880) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (midnight_block_11880_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_11880_memory (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 512) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup7 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap4 (by native_decide) (by evm_ov)
  have r32 := RD.genMstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.dup5 (by native_decide) (by evm_ov)
  have r35 := RD.genKeccak256 r34 (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r37 := RD.genMload r36 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap4 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.dup5 (by native_decide) (by evm_ov)
  have r42 := RD.genMstore r41 (by native_decide) (by evm_ov)
  have r43 := r42.swap1 (by native_decide) (by evm_ov)
  have r44 := r43.dup4 (by native_decide) (by evm_ov)
  have r45 := RD.genKeccak256 r44 (by native_decide) (by evm_ov)
  have r46 := r45.swap3 (by native_decide) (by evm_ov)
  have r47 := RD.genMstore r46 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r49⟩ := RD.sload r48 (by native_decide) (by evm_ov)
  have r50 := r49.swap1 (by native_decide) (by evm_ov)
  have r51 := r50.swap3 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := r52.swap1 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r57 := r56.shl (by native_decide) (by evm_ov)
  have r58 := r57.sub (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.iszero (by native_decide) (by evm_ov)
  have r61 := r60.iszero (by native_decide) (by evm_ov)
  have r62 := r61.dup1 (by native_decide) (by evm_ov)
  have r63 := r62.iszero (by native_decide) (by evm_ov)
  have r64 := r63.push2 (UInt256.ofNat 14521) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11960)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11880_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11880) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (midnight_block_11880_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_11880_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_11880 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11960_taken`. -/
def midnight_block_11960_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11960. -/
theorem midnight_block_11960_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_11960_taken_stack (R := R)) mem aw rdata σ (k + 1) (C + ((10))) := by
  let r0 := h
  have r1 := r0.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11960_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_11960_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11960_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11960_fallthrough`. -/
def midnight_block_11960_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11960. -/
theorem midnight_block_11960_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (midnight_block_11960_fallthrough_stack (R := R)) mem aw rdata σ (k + 1) (C + ((10))) := by
  let r0 := h
  have r1 := r0.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11961)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11960_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (midnight_block_11960_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11960_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11961_taken`. -/
def midnight_block_11961_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11961. -/
theorem midnight_block_11961_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14492) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14492) (midnight_block_11961_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14492) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14492)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11961_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14492) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14492) (midnight_block_11961_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11961_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11961_fallthrough`. -/
def midnight_block_11961_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11961. -/
theorem midnight_block_11961_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11966) (midnight_block_11961_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14492) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11966)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11961_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11961) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11966) (midnight_block_11961_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11961_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11966`. -/
def midnight_block_11966_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 448) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))) :: R)

/-- Final memory for bytecode block summary `midnight_block_11966`. -/
def midnight_block_11966_memory {mem : ByteArray} : ByteArray :=
  ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 448) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11966. -/
theorem midnight_block_11966 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 12021) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11966) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (midnight_block_11966_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11966_memory (mem := mem)) (M (M (M (M (M (M (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r32 := r31.push0 (by native_decide) (by evm_ov)
  have r33 := RD.genKeccak256 r32 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r34⟩ := RD.sload r33 (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.iszero (by native_decide) (by evm_ov)
  have r37 := r36.iszero (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12021)) r39 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11966_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 12021) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11966) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (midnight_block_11966_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (midnight_block_11966_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_11966 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12021_taken`. -/
def midnight_block_12021_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12021. -/
theorem midnight_block_12021_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14463) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14463) (midnight_block_12021_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14463) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14463)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12021_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14463) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14463) (midnight_block_12021_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12021_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12021_fallthrough`. -/
def midnight_block_12021_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12021. -/
theorem midnight_block_12021_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12026) (midnight_block_12021_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14463) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12026)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12021_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12026) (midnight_block_12021_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12021_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12026`. -/
def midnight_block_12026_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: (UInt256.xor (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.mul (UInt256.xor (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (memLoad (UInt256.ofNat 352) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.lt (UInt256.land (memLoad (UInt256.ofNat 352) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))))) :: (UInt256.ofNat 12118) :: (UInt256.ofNat 12138) :: (UInt256.ofNat 12144) :: (UInt256.ofNat 1000000000000000000) :: (UInt256.ofNat 12150) :: (UInt256.land (memLoad (UInt256.ofNat 352) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x2 :: x4 :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x0 :: x1 :: (UInt256.xor (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.mul (UInt256.xor (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (memLoad (UInt256.ofNat 352) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.lt (UInt256.land (memLoad (UInt256.ofNat 352) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))))) :: x3 :: (UInt256.mul (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))) :: R)

/-- Final memory for bytecode block summary `midnight_block_12026`. -/
def midnight_block_12026_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12026. -/
theorem midnight_block_12026 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12026) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12026_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (midnight_block_12026_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0)) (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.dup5 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r14 := r13.calldataload (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r18 := r17.calldataload (by native_decide) (by evm_ov)
  have r19 := r18.gt (by native_decide) (by evm_ov)
  have r20 := r19.mul (by native_decide) (by evm_ov)
  have r21 := r20.swap6 (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.and (by native_decide) (by evm_ov)
  have r34 := r33.swap5 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r36 := r35.calldataload (by native_decide) (by evm_ov)
  have r37 := r36.dup7 (by native_decide) (by evm_ov)
  have r38 := r37.lt (by native_decide) (by evm_ov)
  have r39 := r38.dup7 (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r41 := r40.calldataload (by native_decide) (by evm_ov)
  have r42 := r41.xor (by native_decide) (by evm_ov)
  have r43 := r42.mul (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r45 := r44.calldataload (by native_decide) (by evm_ov)
  have r46 := r45.xor (by native_decide) (by evm_ov)
  have r47 := r46.swap6 (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 12150) (by native_decide) (by evm_ov)
  have r49 := r48.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 12144) (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 12138) (by native_decide) (by evm_ov)
  have r52 := r51.push2 (UInt256.ofNat 12118) (by native_decide) (by evm_ov)
  have r53 := r52.dup12 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r55 := r54.calldataload (by native_decide) (by evm_ov)
  have r56 := r55.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r57 := r56.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r57 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12026_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12026) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12026_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (midnight_block_12026_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12026 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12118`. -/
def midnight_block_12118_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x10 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 112)) (UInt256.ofNat 4294967295)) :: x7 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12118. -/
theorem midnight_block_12118 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12118) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_12118_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap7 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r9 := r8.shr (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20413)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12118_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12118) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_12118_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12118 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end midnightBlocks
