import Reasoning.Reach
import Benchmarks.Safe.V2_0e91d99.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 7828. -/
theorem safeRuntime_block_7828 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7828) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V2_0e91d99.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_7831`. -/
def safeRuntime_block_7831_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.ofNat 6891) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7831. -/
theorem safeRuntime_block_7831 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11048) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7831) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11048) (safeRuntime_block_7831_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6891) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11048) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11048)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7831_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11048) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7831) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11048) (safeRuntime_block_7831_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7831 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7841_taken`. -/
def safeRuntime_block_7841_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7841. -/
theorem safeRuntime_block_7841_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7864) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7841) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7864) (safeRuntime_block_7841_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7864) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7864)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7841_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7864) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7841) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7864) (safeRuntime_block_7841_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7841_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7841_fallthrough`. -/
def safeRuntime_block_7841_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7841. -/
theorem safeRuntime_block_7841_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7841) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7859) (safeRuntime_block_7841_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7864) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7859)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7841_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7841) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7859) (safeRuntime_block_7841_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7841_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7859`. -/
def safeRuntime_block_7859_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7859. -/
theorem safeRuntime_block_7859 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7866) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7859) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (safeRuntime_block_7859_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7866) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7866)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7859_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7866) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7859) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (safeRuntime_block_7859_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7859 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7864. -/
theorem safeRuntime_block_7864 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7864) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7865) R mem aw rdata σ (k + 1) (C + ((1))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7865)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7864_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7864) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7865) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7864 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 7865: unsupported_32 (0x32). No RD transition is asserted. Summaries resume at pc 7866 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_7866_taken`. -/
def safeRuntime_block_7866_taken_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7866. -/
theorem safeRuntime_block_7866_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8028) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8028) (safeRuntime_block_7866_taken_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8028) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8028)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7866_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8028) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8028) (safeRuntime_block_7866_taken_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7866_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7866_fallthrough`. -/
def safeRuntime_block_7866_fallthrough_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7866. -/
theorem safeRuntime_block_7866_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7883) (safeRuntime_block_7866_fallthrough_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8028) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7883)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7866_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7866) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7883) (safeRuntime_block_7866_fallthrough_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7866_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7883`. -/
def safeRuntime_block_7883_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 7916) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7883. -/
theorem safeRuntime_block_7883 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7883) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7886) (safeRuntime_block_7883_stack (R := R)) mem aw rdata σ (k + 1) (C + ((3))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 7916) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7886)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7883_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7883) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7886) (safeRuntime_block_7883_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7883 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 7886: unsupported_3a (0x3a). No RD transition is asserted. Summaries resume at pc 7887 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_7887_taken`. -/
def safeRuntime_block_7887_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7887. -/
theorem safeRuntime_block_7887_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7887) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7898) (safeRuntime_block_7887_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup7 (by native_decide) (by evm_ov)
  have r2 := r1.lt (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7898) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7898)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7887_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7887) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7898) (safeRuntime_block_7887_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7887_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7887_fallthrough`. -/
def safeRuntime_block_7887_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7887. -/
theorem safeRuntime_block_7887_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7887) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7893) (safeRuntime_block_7887_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup7 (by native_decide) (by evm_ov)
  have r2 := r1.lt (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7898) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7893)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7887_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7887) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7893) (safeRuntime_block_7887_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7887_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 7893: unsupported_3a (0x3a). No RD transition is asserted. Summaries resume at pc 7894 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 7894. -/
theorem safeRuntime_block_7894 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7900) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7894) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 7900) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7900)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7894_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7900) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7894) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7894 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7898`. -/
def safeRuntime_block_7898_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7898. -/
theorem safeRuntime_block_7898 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7898) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) (safeRuntime_block_7898_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7900)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7898_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7898) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) (safeRuntime_block_7898_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7898 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7900`. -/
def safeRuntime_block_7900_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: x8 :: (UInt256.ofNat 7910) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7900. -/
theorem safeRuntime_block_7900 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7193) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7193) (safeRuntime_block_7900_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7910) (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  have r4 := r3.dup10 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 7193) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7193)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7900_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7193) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7900) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7193) (safeRuntime_block_7900_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7900 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7910`. -/
def safeRuntime_block_7910_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7910. -/
theorem safeRuntime_block_7910 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6843) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7910) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6843) (safeRuntime_block_7910_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6843) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6843)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7910_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6843) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7910) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6843) (safeRuntime_block_7910_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7910 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7916`. -/
def safeRuntime_block_7916_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((64) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1) :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1) :: (⟨0⟩ : UInt256) :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7916. -/
theorem safeRuntime_block_7916 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7916) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7945) (safeRuntime_block_7916_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((66) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  have r19 := r18.dup4 (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.dup6 (by native_decide) (by evm_ov)
  have r23 := r22.dup8 (by native_decide) (by evm_ov)
  have r24 := RD.genGas (RD.normalizeCounters (k' := k + 23) (C' := C + ((64) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r23 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7945)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7916_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7916) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7945) (safeRuntime_block_7916_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7916 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 7945: call (0xf1). No RD transition is asserted. Summaries resume at pc 7946 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_7946_taken`. -/
def safeRuntime_block_7946_taken_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (UInt256.ofNat rdata.size) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7946. -/
theorem safeRuntime_block_7946_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat rdata.size) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7991) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7991) (safeRuntime_block_7946_taken_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.swap3 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.eq (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7991) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7991)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7946_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat rdata.size) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7991) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7991) (safeRuntime_block_7946_taken_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7946_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7946_fallthrough`. -/
def safeRuntime_block_7946_fallthrough_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (UInt256.ofNat rdata.size) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7946. -/
theorem safeRuntime_block_7946_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat rdata.size) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7959) (safeRuntime_block_7946_fallthrough_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.swap3 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.eq (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7991) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7959)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7946_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat rdata.size) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7959) (safeRuntime_block_7946_fallthrough_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7946_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7959`. -/
def safeRuntime_block_7959_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_7959`. -/
def safeRuntime_block_7959_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (rdata.write (⟨0⟩ : UInt256).toNat ((UInt256.ofNat rdata.size).toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 63)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (UInt256.ofNat rdata.size).toNat)

/-- Automatically generated RD summary for bytecode block at pc 7959. -/
theorem safeRuntime_block_7959 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7996) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7959) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7996) (safeRuntime_block_7959_stack (mem := mem) (x0 := x0) (R := R)) (safeRuntime_block_7959_memory (mem := mem) (rdata := rdata)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (UInt256.ofNat rdata.size)) rdata σ (k + 25) (C + ((72) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (UInt256.ofNat rdata.size)) + (3 + 3 * (((UInt256.ofNat rdata.size).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.returndatasize (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.returndatasize (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := r20.dup5 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genReturndatacopy r22 (by native_decide) hguard0 (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 7996) (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7996)) r25 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7959_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7996) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7959) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7996) (safeRuntime_block_7959_stack (mem := mem) (x0 := x0) (R := R)) (safeRuntime_block_7959_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7959 hstack hguard0 hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7991`. -/
def safeRuntime_block_7991_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7991. -/
theorem safeRuntime_block_7991 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7991) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7996) (safeRuntime_block_7991_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((9))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7996)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7991_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7991) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7996) (safeRuntime_block_7991_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7991 hstack h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V2_0e91d99.RuntimeBlocks
