import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Automatically generated RD summary for bytecode block at pc 1188. -/
theorem midnight_block_1188_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.sub x1 x3) + (UInt256.ofNat 32)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1188) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1202) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup6 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1202)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1188_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.sub x1 x3) + (UInt256.ofNat 32)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1188) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1202) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1188_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1202`. -/
def midnight_block_1202_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 1218) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.ofNat 32) :: (UInt256.ofNat 128) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1202. -/
theorem midnight_block_1202 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18417) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1202) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18417) (midnight_block_1202_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1218) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 18417) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18417)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1202_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18417) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1202) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18417) (midnight_block_1202_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1202 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1218`. -/
def midnight_block_1218_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x6 :: (UInt256.ofNat 1227) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1218. -/
theorem midnight_block_1218 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23130) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1218) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23130) (midnight_block_1218_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1227) (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 23130) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23130)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1218_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23130) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1218) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23130) (midnight_block_1218_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1218 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1227`. -/
def midnight_block_1227_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x7 + (UInt256.ofNat 96)) :: (UInt256.ofNat 1259) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `midnight_block_1227`. -/
def midnight_block_1227_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x7 : UInt256} : ByteArray :=
  ((memLoad (x7 + (UInt256.ofNat 64)) ((memLoad (x7 + x3) (x0.toByteArray.write 0 mem x1.toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem x1.toNat 32) (x1 + x3).toNat 32)).toByteArray.write 0 ((memLoad (x7 + x3) (x0.toByteArray.write 0 mem x1.toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem x1.toNat 32) (x1 + x3).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1227. -/
theorem midnight_block_1227 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23130) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1227) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23130) (midnight_block_1227_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_1227_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x7 := x7)) (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x7 + x3) (⟨32⟩ : UInt256)) (x1 + x3) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 25) (C + ((78) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x7 + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x1 (⟨32⟩ : UInt256)) (x7 + x3) (⟨32⟩ : UInt256)) (x1 + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x1 (⟨32⟩ : UInt256)) (x7 + x3) (⟨32⟩ : UInt256)) (x1 + x3) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x7 + x3) (⟨32⟩ : UInt256)) (x1 + x3) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup8 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 1259) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r22 := r21.dup9 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 23130) (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23130)) r25 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1227_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23130) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1227) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23130) (midnight_block_1227_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_1227_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x7 := x7)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1227 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1259`. -/
def midnight_block_1259_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x3) :: x5 :: x6 :: (x7 + x4) :: R)

/-- Final memory for bytecode block summary `midnight_block_1259`. -/
def midnight_block_1259_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 96)).toNat 32) x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1259. -/
theorem midnight_block_1259 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1092) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1259) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1092) (midnight_block_1259_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_1259_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((42) + (memExpansionCost aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.swap4 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1092) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1092)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1259_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1092) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1259) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1092) (midnight_block_1259_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_1259_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1259 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1275. -/
theorem midnight_block_1275 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1275) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2531341609) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1296. -/
theorem midnight_block_1296_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1296) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1296_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1296) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1296_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1296. -/
theorem midnight_block_1296_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1296) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1302)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1296_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1296) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1296_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1302. -/
theorem midnight_block_1302_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1302_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1302_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1302. -/
theorem midnight_block_1302_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1314) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1314)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1302_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1302) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1314) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1302_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1314`. -/
def midnight_block_1314_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1321) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1314. -/
theorem midnight_block_1314 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18254) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1314) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18254) (midnight_block_1314_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1321) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18254) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18254)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1314_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18254) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1314) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18254) (midnight_block_1314_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1314 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1321. -/
theorem midnight_block_1321_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1415) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1321) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1415) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.caller (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1415) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1415)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1321_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1415) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1321) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1415) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1321_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1321. -/
theorem midnight_block_1321_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1321) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1340) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.caller (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1415) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1340)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1321_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1321) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1340) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1321_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1340. -/
theorem midnight_block_1340 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1340) (x0 :: R) mem aw rdata σ k C)
    : RDret Benchmarks.Midnight.midnightBytecode g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 12) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0))) (mem.readWithPadding (memLoad (UInt256.ofNat 800) mem).toNat (memLoad (UInt256.ofNat 800) mem).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.not (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.or (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sstore r18 hperm (by native_decide) (by evm_ov)
  have r20 := r19.pushConst (UInt256.ofNat 9380160934195850801358680234445299316310518527935727650277444552373081058977) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := RD.genLog2 r24 (by native_decide) hperm (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.dup1 (by native_decide) (by evm_ov)
  exact RD.genRet r28 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1415. -/
theorem midnight_block_1415 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1415) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 54227425) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1436. -/
theorem midnight_block_1436_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1436) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1436_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1436) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1436_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1436. -/
theorem midnight_block_1436_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1436) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1442) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1442)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1436_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1436) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1442) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1436_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1442`. -/
def midnight_block_1442_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 1450) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1442. -/
theorem midnight_block_1442 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18819) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1442) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18819) (midnight_block_1442_stack (ee := ee) (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1450) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18819) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18819)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1442_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18819) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1442) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18819) (midnight_block_1442_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1442 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1450. -/
theorem midnight_block_1450_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1675) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1450) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1675) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.caller (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1675) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1675)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1450_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1675) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1450) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1675) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1450_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1450. -/
theorem midnight_block_1450_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1450) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.caller (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1675) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1469)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1450_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1450) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1450_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end midnightBlocks
