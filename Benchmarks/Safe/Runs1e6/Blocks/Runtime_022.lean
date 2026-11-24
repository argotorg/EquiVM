import Reasoning.Reach
import Benchmarks.Safe.Runs1e6.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_4755`. -/
def safeRuntime_block_4755_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4755. -/
theorem safeRuntime_block_4755 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4827) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4755) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (safeRuntime_block_4755_stack (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem))) rdata σ (k + 10) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem))) + (375 + 8 * (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)).toNat + 2 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := RD.genLog2 r7 (by native_decide) hperm (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 4827) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4827)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4755_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4827) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4755) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (safeRuntime_block_4755_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4755 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4768`. -/
def safeRuntime_block_4768_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 15948521614687691110761868893838234996960037361152471596931148700057464241443) :: x3 :: x0 :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_4768`. -/
def safeRuntime_block_4768_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4768. -/
theorem safeRuntime_block_4768 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4818) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4768) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4818) (safeRuntime_block_4768_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_4768_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((45) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 15948521614687691110761868893838234996960037361152471596931148700057464241443) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 4818) (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4818)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4768_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4818) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4768) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4818) (safeRuntime_block_4768_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_4768_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4768 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4818`. -/
def safeRuntime_block_4818_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4818. -/
theorem safeRuntime_block_4818 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4818) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (safeRuntime_block_4818_stack (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem))) rdata σ (k + 8) (C + ((19) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem))) + (375 + 8 * (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)).toNat + 2 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := RD.genLog2 r7 (by native_decide) hperm (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4827)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4818_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4818) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (safeRuntime_block_4818_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4818 hstack hperm h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4827_taken`. -/
def safeRuntime_block_4827_taken_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4827. -/
theorem safeRuntime_block_4827_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4989) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (safeRuntime_block_4827_taken_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 4989) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4989)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4827_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4989) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (safeRuntime_block_4827_taken_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4827_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4827_fallthrough`. -/
def safeRuntime_block_4827_fallthrough_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4827. -/
theorem safeRuntime_block_4827_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (safeRuntime_block_4827_fallthrough_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 4989) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4858)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4827_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4827) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (safeRuntime_block_4827_fallthrough_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4858_taken`. -/
def safeRuntime_block_4858_taken_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) :: (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (⟨0⟩ : UInt256) :: ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 2468811624) :: (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_4858_taken`. -/
def safeRuntime_block_4858_taken_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4858. -/
theorem safeRuntime_block_4858_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4966) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4966) (safeRuntime_block_4858_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_4858_taken_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 2468811624) (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.dup4 (by native_decide) (by evm_ov)
  have r32 := r31.sub (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.push0 (by native_decide) (by evm_ov)
  have r35 := r34.dup8 (by native_decide) (by evm_ov)
  have r36 := r35.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r37⟩ := r36.extcodesize (by native_decide) (by evm_ov)
  have r38 := r37.iszero (by native_decide) (by evm_ov)
  have r39 := r38.dup1 (by native_decide) (by evm_ov)
  have r40 := r39.iszero (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 4966) (by native_decide) (by evm_ov)
  have r42 := r41.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4966)) r42 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4858_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4966) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4966) (safeRuntime_block_4858_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_4858_taken_memory (mem := mem) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4858_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4858_fallthrough`. -/
def safeRuntime_block_4858_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) :: (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (⟨0⟩ : UInt256) :: ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 2468811624) :: (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_4858_fallthrough`. -/
def safeRuntime_block_4858_fallthrough_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4858. -/
theorem safeRuntime_block_4858_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4963) (safeRuntime_block_4858_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_4858_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 66559029714281558484110900056217435723262332508534932952963113331629997686784) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 2468811624) (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.dup4 (by native_decide) (by evm_ov)
  have r32 := r31.sub (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.push0 (by native_decide) (by evm_ov)
  have r35 := r34.dup8 (by native_decide) (by evm_ov)
  have r36 := r35.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r37⟩ := r36.extcodesize (by native_decide) (by evm_ov)
  have r38 := r37.iszero (by native_decide) (by evm_ov)
  have r39 := r38.dup1 (by native_decide) (by evm_ov)
  have r40 := r39.iszero (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 4966) (by native_decide) (by evm_ov)
  have r42 := r41.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4963)) r42 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4858_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4858) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4963) (safeRuntime_block_4858_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_4858_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4858_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4963. -/
theorem safeRuntime_block_4963 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4963) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_4966`. -/
def safeRuntime_block_4966_stack {g : Sat256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((3)) + 2)).toUInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4966. -/
theorem safeRuntime_block_4966 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4966) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4969) (safeRuntime_block_4966_stack (g := g) (C := C) (R := R)) mem aw rdata σ (k + 3) (C + ((5))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4969)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4966_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4966) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4969) (safeRuntime_block_4966_stack (g := g) (C := C) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4966 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 4969: call (0xf1). No RD transition is asserted. Summaries resume at pc 4970 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_4970_taken`. -/
def safeRuntime_block_4970_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4970. -/
theorem safeRuntime_block_4970_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4984) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4984) (safeRuntime_block_4970_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4984) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4984)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4970_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4984) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4984) (safeRuntime_block_4970_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4970_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4970_fallthrough`. -/
def safeRuntime_block_4970_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4970. -/
theorem safeRuntime_block_4970_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4977) (safeRuntime_block_4970_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4984) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4977)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4970_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4977) (safeRuntime_block_4970_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4970_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4977. -/
theorem safeRuntime_block_4977 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4977) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by native_decide) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r6 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_4984`. -/
def safeRuntime_block_4984_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4984. -/
theorem safeRuntime_block_4984 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4984) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (safeRuntime_block_4984_stack (R := R)) mem aw rdata σ (k + 5) (C + ((9))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4989)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4984_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4984) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (safeRuntime_block_4984_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4984 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4989`. -/
def safeRuntime_block_4989_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4989. -/
theorem safeRuntime_block_4989 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x14 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x14 (safeRuntime_block_4989_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 17) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap12 (by native_decide) (by evm_ov)
  have r5 := r4.swap11 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.pop (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4989_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x14 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4989) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x14 (safeRuntime_block_4989_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4989 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5006`. -/
def safeRuntime_block_5006_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: (UInt256.ofNat ee.source.val) :: (UInt256.ofNat 5017) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5006. -/
theorem safeRuntime_block_5006 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7903) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5006) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7903) (safeRuntime_block_5006_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5017) (by native_decide) (by evm_ov)
  have r3 := r2.caller (by native_decide) (by evm_ov)
  have r4 := r3.dup6 (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 7903) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7903)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5006_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7903) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5006) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7903) (safeRuntime_block_5006_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5006 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5017`. -/
def safeRuntime_block_5017_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5017. -/
theorem safeRuntime_block_5017 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5017) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x4 (safeRuntime_block_5017_stack (R := R)) mem aw rdata σ (k + 6) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5017_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5017) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x4 (safeRuntime_block_5017_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5017 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5023_taken`. -/
def safeRuntime_block_5023_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5023. -/
theorem safeRuntime_block_5023_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 5053) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5023) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5053) (safeRuntime_block_5023_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5053) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5053)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5023_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 5053) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5023) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5053) (safeRuntime_block_5023_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5023_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5023_fallthrough`. -/
def safeRuntime_block_5023_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5023. -/
theorem safeRuntime_block_5023_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5023) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5046) (safeRuntime_block_5023_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5053) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5046)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5023_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5023) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5046) (safeRuntime_block_5023_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5023_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5046`. -/
def safeRuntime_block_5046_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5053) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5046. -/
theorem safeRuntime_block_5046 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11708) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5046) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11708) (safeRuntime_block_5046_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5053) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11708) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11708)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5046_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11708) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5046) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11708) (safeRuntime_block_5046_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5046 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5053_taken`. -/
def safeRuntime_block_5053_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5053_taken`. -/
def safeRuntime_block_5053_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5053. -/
theorem safeRuntime_block_5053_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 5094) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5053) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5094) (safeRuntime_block_5053_taken_stack (mem := mem) (x0 := x0) (R := R)) (safeRuntime_block_5053_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 5094) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5094)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5053_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 5094) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5053) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 5094) (safeRuntime_block_5053_taken_stack (mem := mem) (x0 := x0) (R := R)) (safeRuntime_block_5053_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5053_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.Runs1e6.RuntimeBlocks
