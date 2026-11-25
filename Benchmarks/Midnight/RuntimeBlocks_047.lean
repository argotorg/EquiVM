import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_12275_taken`. -/
def midnight_block_12275_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12275. -/
theorem midnight_block_12275_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14257) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12275) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14257) (midnight_block_12275_taken_stack (mem := mem) (R := R)) mem (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((64) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 14257) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14257)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12275_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14257) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12275) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14257) (midnight_block_12275_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12275_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12275_fallthrough`. -/
def midnight_block_12275_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12275. -/
theorem midnight_block_12275_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12275) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (midnight_block_12275_fallthrough_stack (mem := mem) (R := R)) mem (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((64) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 14257) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12302)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12275_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 192)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12275) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (midnight_block_12275_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12275_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12302. -/
theorem midnight_block_12302_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14160) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14160) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14160) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14160)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12302_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14160) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14160) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12302_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12302. -/
theorem midnight_block_12302_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14160) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12309)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12302_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12302_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12309_taken`. -/
def midnight_block_12309_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12309. -/
theorem midnight_block_12309_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14145) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14145) (midnight_block_12309_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14145) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14145)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12309_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14145) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14145) (midnight_block_12309_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12309_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12309_fallthrough`. -/
def midnight_block_12309_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12309. -/
theorem midnight_block_12309_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12316) (midnight_block_12309_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14145) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12316)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12309_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12309) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12316) (midnight_block_12309_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12309_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12316`. -/
def midnight_block_12316_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x7 :: (UInt256.ofNat 4204) :: (UInt256.ofNat 6795) :: x2 :: (UInt256.ofNat 12353) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) :: x0 :: x1 :: (UInt256.ofNat 12505) :: (UInt256.ofNat 2) :: (UInt256.ofNat 12517) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12316. -/
theorem midnight_block_12316 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12316) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12316_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 20) (C + ((65))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 12505) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12517) (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 12353) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.swap8 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 6795) (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 4204) (by native_decide) (by evm_ov)
  have r16 := r15.dup16 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r18 := r17.calldataload (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12316_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12316) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12316_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12316 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12353`. -/
def midnight_block_12353_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((sstoreAccountMap ee.codeOwner σ (x2 + x5) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + x5) (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) :: (memLoad (UInt256.ofNat 224) mem) :: (UInt256.ofNat 4216) :: (UInt256.ofNat 12386) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12353. -/
theorem midnight_block_12353 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12353_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (x2 + x5) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + x5) (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup6 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.or (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 12386) (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 4216) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r20 := r19.shr (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12353_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12353_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (x2 + x5) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x2 + x5) (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12353 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12386`. -/
def midnight_block_12386_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x10 :: (UInt256.ofNat 12399) :: (UInt256.ofNat 12408) :: x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12386. -/
theorem midnight_block_12386 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12386) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12386_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12408) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 12399) (by native_decide) (by evm_ov)
  have r5 := r4.dup14 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12386_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12386) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12386_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12386 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12399`. -/
def midnight_block_12399_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x3 (⟨0⟩ : UInt256))) x2) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12399. -/
theorem midnight_block_12399 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12399) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12399_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12399_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12399) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12399_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12399 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12408`. -/
def midnight_block_12408_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) :: (memLoad (UInt256.ofNat 160) mem) :: (UInt256.ofNat 12437) :: (UInt256.ofNat 12469) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12408. -/
theorem midnight_block_12408 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12408) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_12408_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.or (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sstore r9 hperm (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 12469) (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 12437) (by native_decide) (by evm_ov)
  have r13 := r12.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r16 := r15.shr (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12408_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12408) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_12408_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot x7)) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12408 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12437`. -/
def midnight_block_12437_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12437. -/
theorem midnight_block_12437 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12437) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_12437_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x7 (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x7 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.not (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.or (by native_decide) (by evm_ov)
  have r23 := r22.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sstore r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r25⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12437_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12437) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_12437_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x7 (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x7 (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12437 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12469`. -/
def midnight_block_12469_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: (UInt256.ofNat 12482) :: (UInt256.ofNat 12491) :: x4 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12469. -/
theorem midnight_block_12469 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12469) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12469_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12491) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 12482) (by native_decide) (by evm_ov)
  have r5 := r4.dup11 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12469_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12469) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12469_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12469 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12482`. -/
def midnight_block_12482_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) x2) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12482. -/
theorem midnight_block_12482 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12482) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_12482_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12482_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12482) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_12482_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12482 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12491`. -/
def midnight_block_12491_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12491. -/
theorem midnight_block_12491 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12491_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x7 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x7 (⟨0⟩ : UInt256))) (UInt256.lnot x6)) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup6 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.or (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sstore r9 hperm (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12491_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12491) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_12491_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x7 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x7 (⟨0⟩ : UInt256))) (UInt256.lnot x6)) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12491 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12505`. -/
def midnight_block_12505_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x4 + x1) (⟨0⟩ : UInt256))) x3) :: x0 :: x2 :: x3 :: (x4 + x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12505. -/
theorem midnight_block_12505 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12505_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12505_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_12505_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12505 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12517`. -/
def midnight_block_12517_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x3 (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x6 :: (UInt256.ofNat 12561) :: x4 :: (UInt256.ofNat 4204) :: (UInt256.ofNat 12566) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12517. -/
theorem midnight_block_12517 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12517) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_12517_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 12566) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 4204) (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 12561) (by native_decide) (by evm_ov)
  have r24 := r23.dup9 (by native_decide) (by evm_ov)
  have r25 := r24.dup6 (by native_decide) (by evm_ov)
  have r26 := r25.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r27⟩ := RD.sload r26 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12517_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12517) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_12517_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12517 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12561. -/
theorem midnight_block_12561 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12561) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12561_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12561) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12561 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12566`. -/
def midnight_block_12566_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 256) mem) :: (memLoad (UInt256.ofNat 416) mem) :: (UInt256.ofNat 12598) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12566. -/
theorem midnight_block_12566 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12566) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12566_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 12598) (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12566_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12566) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_12566_stack (mem := mem) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12566 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12598`. -/
def midnight_block_12598_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 6).toByteArray.write 0 ((UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: (UInt256.ofNat 12638) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 6).toByteArray.write 0 ((UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_12598`. -/
def midnight_block_12598_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 6).toByteArray.write 0 ((UInt256.land (memLoad ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12598. -/
theorem midnight_block_12598 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12598) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_12598_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_12598_memory (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) mem) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 12638) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.swap2 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r27 := r26.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r27 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12598_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12598) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_12598_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_12598_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12598 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end midnightBlocks
