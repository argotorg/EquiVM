import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_5961_fallthrough`. -/
def midnight_block_5961_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + x0) :: x1 :: x2 :: x3 :: x4 :: (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + x0) + (UInt256.ofNat 36)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5961. -/
theorem midnight_block_5961_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + x0) + (UInt256.ofNat 4)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5961) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (midnight_block_5961_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 19) (C + ((64))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.swap6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5988)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5961_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + x0) + (UInt256.ofNat 4)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5961) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (midnight_block_5961_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5961_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5988. -/
theorem midnight_block_5988_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sgt x6 (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)) (UInt256.ofNat 7)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ (k + 12) (C + ((42))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.calldatasize (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup8 (by native_decide) (by evm_ov)
  have r10 := r9.sgt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5988_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sgt x6 (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)) (UInt256.ofNat 7)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5988_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5988. -/
theorem midnight_block_5988_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sgt x6 (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)) (UInt256.ofNat 7)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6004) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ (k + 12) (C + ((42))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.calldatasize (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup8 (by native_decide) (by evm_ov)
  have r10 := r9.sgt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6004)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5988_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sgt x6 (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)) (UInt256.ofNat 7)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5988) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6004) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5988_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6004`. -/
def midnight_block_6004_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 800) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 256).toByteArray.write 0 mem (x8 + (UInt256.ofNat 420)).toNat 32) x0.toNat 32)) :: x1 :: x6 :: x2 :: x3 :: x4 :: x5 :: (x8 + (UInt256.ofNat 612)) :: x8 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `midnight_block_6004`. -/
def midnight_block_6004_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x8 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 256).toByteArray.write 0 mem (x8 + (UInt256.ofNat 420)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6004. -/
theorem midnight_block_6004 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6004) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (midnight_block_6004_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_6004_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x8 := x8)) (M (M (M aw (x8 + (UInt256.ofNat 420)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) rdata σ (k + 25) (C + ((75) + (memExpansionCost aw (x8 + (UInt256.ofNat 420)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x8 + (UInt256.ofNat 420)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x8 + (UInt256.ofNat 420)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 420) (by native_decide) (by evm_ov)
  have r3 := r2.dup11 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.calldataload (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.dup9 (by native_decide) (by evm_ov)
  have r15 := r14.swap7 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 612) (by native_decide) (by evm_ov)
  have r17 := r16.dup9 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.swap7 (by native_decide) (by evm_ov)
  have r20 := r19.swap6 (by native_decide) (by evm_ov)
  have r21 := r20.swap5 (by native_decide) (by evm_ov)
  have r22 := r21.swap4 (by native_decide) (by evm_ov)
  have r23 := r22.swap3 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6038)) r25 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6004_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6004) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (midnight_block_6004_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_6004_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6004 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6038. -/
theorem midnight_block_6038_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6376) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6376) (x0 :: x1 :: R) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6376) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6376)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6038_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6376) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6376) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6038_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6038. -/
theorem midnight_block_6038_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6050) (x0 :: x1 :: R) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6376) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6050)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6038_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 4)).toNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6038) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6050) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6038_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6050`. -/
def midnight_block_6050_stack {ee : ExecutionEnv} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + (UInt256.ofNat 196)) :: (UInt256.ofNat 6114) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x3 :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x4 :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x5 :: x6 :: x7 :: (UInt256.ofNat 6199) :: x9 :: x8 :: x8 :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `midnight_block_6050`. -/
def midnight_block_6050_memory {ee : ExecutionEnv} {mem : ByteArray} {x8 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + (UInt256.ofNat 164)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 mem (x8 + (UInt256.ofNat 452)).toNat 32) (x8 + (UInt256.ofNat 484)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6050. -/
theorem midnight_block_6050 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6050) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_6050_stack (ee := ee) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (midnight_block_6050_memory (ee := ee) (mem := mem) (x8 := x8)) (M (M aw (x8 + (UInt256.ofNat 452)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 484)) (⟨32⟩ : UInt256)) rdata σ (k + 44) (C + ((134) + (memExpansionCost aw (x8 + (UInt256.ofNat 452)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x8 + (UInt256.ofNat 452)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 484)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6199) (by native_decide) (by evm_ov)
  have r6 := r5.swap3 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup8 (by native_decide) (by evm_ov)
  have r13 := r12.swap7 (by native_decide) (by evm_ov)
  have r14 := r13.swap4 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := r16.swap11 (by native_decide) (by evm_ov)
  have r18 := r17.swap8 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r21 := r20.calldataload (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := r22.calldataload (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 452) (by native_decide) (by evm_ov)
  have r25 := r24.dup12 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r30 := r29.calldataload (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.calldataload (by native_decide) (by evm_ov)
  have r33 := r32.push2 (UInt256.ofNat 484) (by native_decide) (by evm_ov)
  have r34 := r33.dup12 (by native_decide) (by evm_ov)
  have r35 := r34.add (by native_decide) (by evm_ov)
  have r36 := RD.genMstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.dup2 (by native_decide) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 6114) (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r41 := r40.calldataload (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r44 := r43.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r44 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6050_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6050) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_6050_stack (ee := ee) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (midnight_block_6050_memory (ee := ee) (mem := mem) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6050 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6114`. -/
def midnight_block_6114_stack {ee : ExecutionEnv} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + (UInt256.ofNat 228)) :: (UInt256.ofNat 6136) :: x3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `midnight_block_6114`. -/
def midnight_block_6114_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x11 : UInt256} : ByteArray :=
  ((UInt256.land x0 x1).toByteArray.write 0 mem (x11 + (UInt256.ofNat 516)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6114. -/
theorem midnight_block_6114 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6114) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_6114_stack (ee := ee) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (midnight_block_6114_memory (mem := mem) (x0 := x0) (x1 := x1) (x11 := x11)) (M aw (x11 + (UInt256.ofNat 516)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((45) + (memExpansionCost aw (x11 + (UInt256.ofNat 516)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 516) (by native_decide) (by evm_ov)
  have r4 := r3.dup12 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6136) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.calldataload (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6114_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6114) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_6114_stack (ee := ee) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (midnight_block_6114_memory (mem := mem) (x0 := x0) (x1 := x1) (x11 := x11)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6114 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6136`. -/
def midnight_block_6136_stack {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `midnight_block_6136`. -/
def midnight_block_6136_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x8 : UInt256} {x11 : UInt256} : ByteArray :=
  (((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.sub x8 x11)).toByteArray.write 0 ((UInt256.land x4 x5).toByteArray.write 0 ((UInt256.land x2 x3).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 640) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem (x11 + (UInt256.ofNat 548)).toNat 32) (x11 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem (x11 + (UInt256.ofNat 548)).toNat 32) (x11 + (UInt256.ofNat 100)).toNat 32) (x11 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 640) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem (x11 + (UInt256.ofNat 548)).toNat 32) (x11 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem (x11 + (UInt256.ofNat 548)).toNat 32) (x11 + (UInt256.ofNat 100)).toNat 32) (x11 + (UInt256.ofNat 132)).toNat 32) (x11 + (UInt256.ofNat 164)).toNat 32) (x11 + (UInt256.ofNat 196)).toNat 32) (x11 + (UInt256.ofNat 228)).toNat 32) (x11 + (UInt256.ofNat 260)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6136. -/
theorem midnight_block_6136 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19711) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6136) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19711) (midnight_block_6136_stack (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (midnight_block_6136_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x8 := x8) (x11 := x11)) (M (M (M (M (M (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 196)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 228)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 260)) (⟨32⟩ : UInt256)) rdata σ (k + 46) (C + ((141) + (memExpansionCost aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 196)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 196)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 228)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x11 + (UInt256.ofNat 548)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 196)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 228)) (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 260)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 548) (by native_decide) (by evm_ov)
  have r4 := r3.dup12 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r8 := r7.calldataload (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r10 := r9.dup12 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r16 := r15.dup12 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r22 := r21.dup12 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r27 := r26.dup10 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r32 := r31.dup8 (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := RD.genMstore r33 (by native_decide) (by evm_ov)
  have r35 := r34.dup6 (by native_decide) (by evm_ov)
  have r36 := r35.dup4 (by native_decide) (by evm_ov)
  have r37 := r36.sub (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r39 := r38.not (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r42 := r41.dup8 (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := RD.genMstore r43 (by native_decide) (by evm_ov)
  have r45 := r44.push2 (UInt256.ofNat 19711) (by native_decide) (by evm_ov)
  have r46 := r45.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19711)) r46 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6136_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19711) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6136) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19711) (midnight_block_6136_stack (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (midnight_block_6136_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x8 := x8) (x11 := x11)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6136 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6199`. -/
def midnight_block_6199_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((52) + (memExpansionCost aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.land (memLoad (UInt256.ofNat 736) (x1.toByteArray.write 0 mem (x2 + (UInt256.ofNat 292)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 800) (x1.toByteArray.write 0 mem (x2 + (UInt256.ofNat 292)).toNat 32)) :: x3 :: (UInt256.sub x0 x2) :: x3 :: R)

/-- Final memory for bytecode block summary `midnight_block_6199`. -/
def midnight_block_6199_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem (x2 + (UInt256.ofNat 292)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6199. -/
theorem midnight_block_6199 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6199) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6227) (midnight_block_6199_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_6199_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((54) + (memExpansionCost aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 292) (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := RD.genGas (RD.normalizeCounters (k' := k + 18) (C' := C + ((52) + (memExpansionCost aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 292)) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)))) r18 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6227)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6199_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6199) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6227) (midnight_block_6199_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_6199_memory (mem := mem) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6199 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 6227: call (0xf1). No RD transition is asserted. Summaries resume at pc 6228 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 6228. -/
theorem midnight_block_6228_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6362) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6228) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6362) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6362) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6362)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6228_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6362) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6228) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6362) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6228_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6228. -/
theorem midnight_block_6228_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6228) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6362) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6234)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6228_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6228) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6228_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6234_taken`. -/
def midnight_block_6234_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 800) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6234. -/
theorem midnight_block_6234_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6295) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (midnight_block_6234_taken_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((22) + (memExpansionCost aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6295) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6295)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6234_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6295) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (midnight_block_6234_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6234_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6234_fallthrough`. -/
def midnight_block_6234_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 800) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6234. -/
theorem midnight_block_6234_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (midnight_block_6234_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((22) + (memExpansionCost aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6295) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6243)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6234_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6234) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (midnight_block_6234_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6234_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6243_taken`. -/
def midnight_block_6243_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_6243_taken`. -/
def midnight_block_6243_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (⟨0⟩ : UInt256) mem).toByteArray.write 0 (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6243. -/
theorem midnight_block_6243_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6274) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6274) (midnight_block_6243_taken_stack (R := R)) (midnight_block_6243_taken_memory (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 24513) (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 6274) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6274)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6243_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6274) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6274) (midnight_block_6243_taken_stack (R := R)) (midnight_block_6243_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6243_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6243_fallthrough`. -/
def midnight_block_6243_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_6243_fallthrough`. -/
def midnight_block_6243_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (⟨0⟩ : UInt256) mem).toByteArray.write 0 (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6243. -/
theorem midnight_block_6243_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6265) (midnight_block_6243_fallthrough_stack (R := R)) (midnight_block_6243_fallthrough_memory (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 24513) (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 6274) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6265)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6243_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6243) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6265) (midnight_block_6243_fallthrough_stack (R := R)) (midnight_block_6243_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6243_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6265`. -/
def midnight_block_6265_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x1 :: x1 :: x1 :: x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6265. -/
theorem midnight_block_6265 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 5773) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6265) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5773) (midnight_block_6265_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5773) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5773)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6265_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 5773) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6265) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5773) (midnight_block_6265_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6265 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6274. -/
theorem midnight_block_6274 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6274) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1890925899) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `midnight_block_6295_taken`. -/
def midnight_block_6295_taken_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 32) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6295. -/
theorem midnight_block_6295_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6354) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6354) (midnight_block_6295_taken_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6354) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6354)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6295_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6354) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6354) (midnight_block_6295_taken_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6295_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_6295_fallthrough`. -/
def midnight_block_6295_fallthrough_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 32) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6295. -/
theorem midnight_block_6295_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6308) (midnight_block_6295_fallthrough_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6354) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6308)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_6295_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6295) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6308) (midnight_block_6295_fallthrough_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_6295_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
