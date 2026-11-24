import Reasoning.Reach
import Benchmarks.Safe.Runs1e6.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_2609`. -/
def safeRuntime_block_2609_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2609. -/
theorem safeRuntime_block_2609 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2609) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (safeRuntime_block_2609_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2611)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2609_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2609) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (safeRuntime_block_2609_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2609 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2611_taken`. -/
def safeRuntime_block_2611_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2611. -/
theorem safeRuntime_block_2611_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2657) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2657) (safeRuntime_block_2611_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2657) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2657)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2611_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2657) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2657) (safeRuntime_block_2611_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2611_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2611_fallthrough`. -/
def safeRuntime_block_2611_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2611. -/
theorem safeRuntime_block_2611_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2617) (safeRuntime_block_2611_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2657) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2617)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2611_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2611) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2617) (safeRuntime_block_2611_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2611_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2617`. -/
def safeRuntime_block_2617_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 32261193193507987111894418122780502378982824017997937204356429715986614059008) :: (UInt256.ofNat 2657) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2617. -/
theorem safeRuntime_block_2617 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2617) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_2617_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 2657) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 32261193193507987111894418122780502378982824017997937204356429715986614059008) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8421) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8421)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2617_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2617) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_2617_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2617 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2657`. -/
def safeRuntime_block_2657_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2657. -/
theorem safeRuntime_block_2657 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2949) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2657) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2657_stack (R := R)) mem aw rdata σ (k + 6) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2949) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2949)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2657_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2949) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2657) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2657_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2657 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2665. -/
theorem safeRuntime_block_2665_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x3 (UInt256.ofNat 30))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2856) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2665) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2856) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 30) (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2856) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2856)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2665_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x3 (UInt256.ofNat 30))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2856) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2665) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2856) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2665_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2665. -/
theorem safeRuntime_block_2665_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x3 (UInt256.ofNat 30))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2665) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2675) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 30) (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2856) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2675)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2665_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x3 (UInt256.ofNat 30))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2665) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2675) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2665_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2675`. -/
def safeRuntime_block_2675_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.ofNat 4) :: (UInt256.ofNat 2763) :: (keccakWord ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (memLoad (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)) (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)) :: (UInt256.ofNat 1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_2675`. -/
def safeRuntime_block_2675_memory {mem : ByteArray} {x8 : UInt256} : ByteArray :=
  (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2675. -/
theorem safeRuntime_block_2675 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13886) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13886) (safeRuntime_block_2675_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (safeRuntime_block_2675_memory (mem := mem) (x8 := x8)) (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (memLoad (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32))) rdata σ (k + 42) (C + ((128) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (memLoad (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32))) + (30 + 6 * (((memLoad (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)) (((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 ((UInt256.sub (UInt256.sub ((UInt256.ofNat 92) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32))) (UInt256.ofNat 32)).toByteArray.write 0 (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32) (memLoad (UInt256.ofNat 64) (x8.toByteArray.write 0 ((UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 60)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 11430537079145650693387304458692941425836787954612963690241153482819318579200) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 60) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.dup11 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 92) (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.dup4 (by native_decide) (by evm_ov)
  have r23 := r22.sub (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := RD.genMload r30 (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := RD.genKeccak256 r34 (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r37 := r36.dup7 (by native_decide) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 2763) (by native_decide) (by evm_ov)
  have r39 := r38.swap2 (by native_decide) (by evm_ov)
  have r40 := r39.swap1 (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 13886) (by native_decide) (by evm_ov)
  have r42 := r41.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13886)) r42 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2675_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13886) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13886) (safeRuntime_block_2675_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (safeRuntime_block_2675_memory (mem := mem) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2675 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2763`. -/
def safeRuntime_block_2763_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((150) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x2 :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 (x5.toByteArray.write 0 ((UInt256.land x0 (UInt256.ofNat 255)).toByteArray.write 0 (x1.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 160) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 (x5.toByteArray.write 0 ((UInt256.land x0 (UInt256.ofNat 255)).toByteArray.write 0 (x1.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32))) :: (UInt256.sub (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 (x5.toByteArray.write 0 ((UInt256.land x0 (UInt256.ofNat 255)).toByteArray.write 0 (x1.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)) (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 160) + (memLoad (UInt256.ofNat 64) mem)) :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_2763`. -/
def safeRuntime_block_2763_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} {x5 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 (x5.toByteArray.write 0 ((UInt256.land x0 (UInt256.ofNat 255)).toByteArray.write 0 (x1.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2763. -/
theorem safeRuntime_block_2763 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2763) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2824) (safeRuntime_block_2763_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_2763_memory (mem := mem) (x0 := x0) (x1 := x1) (x4 := x4) (x5 := x5)) (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 52) (C + ((152) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.swap4 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.swap4 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := r28.dup6 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := RD.genMstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.dup5 (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := RD.genMstore r36 (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r42 := RD.genMload r41 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r44 := r43.dup2 (by native_decide) (by evm_ov)
  have r45 := r44.sub (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.dup1 (by native_decide) (by evm_ov)
  have r48 := r47.dup5 (by native_decide) (by evm_ov)
  have r49 := r48.sub (by native_decide) (by evm_ov)
  have r50 := r49.swap1 (by native_decide) (by evm_ov)
  have r51 := r50.dup6 (by native_decide) (by evm_ov)
  have r52 := RD.genGas (RD.normalizeCounters (k' := k + 51) (C' := C + ((150) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r51 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2824)) r52 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2763_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2763) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2824) (safeRuntime_block_2763_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_2763_memory (mem := mem) (x0 := x0) (x1 := x1) (x4 := x4) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2763 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 2824: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 2825 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_2825_taken`. -/
def safeRuntime_block_2825_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2825. -/
theorem safeRuntime_block_2825_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2839) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2825) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2839) (safeRuntime_block_2825_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2839) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2839)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2825_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2839) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2825) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2839) (safeRuntime_block_2825_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2825_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2825_fallthrough`. -/
def safeRuntime_block_2825_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2825. -/
theorem safeRuntime_block_2825_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2825) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2832) (safeRuntime_block_2825_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2839) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2832)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2825_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2825) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2832) (safeRuntime_block_2825_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2825_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2832. -/
theorem safeRuntime_block_2832 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2832) R mem aw rdata σ k C)
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

/-- Final stack for bytecode block summary `safeRuntime_block_2839`. -/
def safeRuntime_block_2839_stack {mem : ByteArray} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x5 :: x6 :: (memLoad (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2839. -/
theorem safeRuntime_block_2839 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2949) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2839) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2839_stack (mem := mem) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap5 (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2949) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2949)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2839_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2949) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2839) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2839_stack (mem := mem) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2839 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2856`. -/
def safeRuntime_block_2856_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((159) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 1) :: (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.land x3 (UInt256.ofNat 255)).toByteArray.write 0 (x8.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 160) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.land x3 (UInt256.ofNat 255)).toByteArray.write 0 (x8.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32))) :: (UInt256.sub (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.land x3 (UInt256.ofNat 255)).toByteArray.write 0 (x8.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)) (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 160) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_2856`. -/
def safeRuntime_block_2856_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x8 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.land x3 (UInt256.ofNat 255)).toByteArray.write 0 (x8.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2856. -/
theorem safeRuntime_block_2856 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2856) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2921) (safeRuntime_block_2856_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (safeRuntime_block_2856_memory (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x8 := x8)) (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 55) (C + ((161) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.dup12 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r18 := r17.dup7 (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := r22.swap2 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r28 := r27.dup2 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := r29.dup5 (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  have r32 := RD.genMstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.add (by native_decide) (by evm_ov)
  have r36 := r35.dup4 (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.swap1 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r47 := r46.dup2 (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.dup1 (by native_decide) (by evm_ov)
  have r51 := r50.dup5 (by native_decide) (by evm_ov)
  have r52 := r51.sub (by native_decide) (by evm_ov)
  have r53 := r52.swap1 (by native_decide) (by evm_ov)
  have r54 := r53.dup6 (by native_decide) (by evm_ov)
  have r55 := RD.genGas (RD.normalizeCounters (k' := k + 54) (C' := C + ((159) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r54 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2921)) r55 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2856_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2856) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2921) (safeRuntime_block_2856_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (safeRuntime_block_2856_memory (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2856 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 2921: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 2922 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_2922_taken`. -/
def safeRuntime_block_2922_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2922. -/
theorem safeRuntime_block_2922_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2936) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2922) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2936) (safeRuntime_block_2922_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2936) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2936)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2922_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2936) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2922) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2936) (safeRuntime_block_2922_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2922_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2922_fallthrough`. -/
def safeRuntime_block_2922_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2922. -/
theorem safeRuntime_block_2922_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2922) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2929) (safeRuntime_block_2922_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2936) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2929)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2922_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2922) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2929) (safeRuntime_block_2922_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2922_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2929. -/
theorem safeRuntime_block_2929 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2929) R mem aw rdata σ k C)
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

/-- Final stack for bytecode block summary `safeRuntime_block_2936`. -/
def safeRuntime_block_2936_stack {mem : ByteArray} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x5 :: x6 :: (memLoad (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2936. -/
theorem safeRuntime_block_2936 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2936_stack (mem := mem) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap5 (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2949)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2936_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (safeRuntime_block_2936_stack (mem := mem) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2936 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2949_taken`. -/
def safeRuntime_block_2949_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2949. -/
theorem safeRuntime_block_2949_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 3044) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3044) (safeRuntime_block_2949_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.dup6 (by native_decide) (by evm_ov)
  have r6 := r5.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 3044) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3044)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2949_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 3044) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3044) (safeRuntime_block_2949_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2949_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_2949_fallthrough`. -/
def safeRuntime_block_2949_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2949. -/
theorem safeRuntime_block_2949_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3003) (safeRuntime_block_2949_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.dup6 (by native_decide) (by evm_ov)
  have r6 := r5.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 3044) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3003)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_2949_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x4) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x5))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2949) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3003) (safeRuntime_block_2949_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_2949_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.Runs1e6.RuntimeBlocks
