import Reasoning.Reach
import Benchmarks.Safe.ViaIR.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR.RuntimeBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `safeRuntime_block_4165`. -/
def safeRuntime_block_4165_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4165. -/
theorem safeRuntime_block_4165 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 4105) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4165) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4105) (safeRuntime_block_4165_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4105) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4105)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4165_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 4105) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4165) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4105) (safeRuntime_block_4165_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4165 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4171`. -/
def safeRuntime_block_4171_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: (UInt256.ofNat 585) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_4171`. -/
def safeRuntime_block_4171_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4171. -/
theorem safeRuntime_block_4171 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7437) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4171) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7437) (safeRuntime_block_4171_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_4171_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((51) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 585) (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup8 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 7437) (by native_decide) (by evm_ov)
  have r16 := r15.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7437)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4171_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7437) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4171) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7437) (safeRuntime_block_4171_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_4171_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4171 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4193_taken`. -/
def safeRuntime_block_4193_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4193. -/
theorem safeRuntime_block_4193_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4193) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) (safeRuntime_block_4193_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 589)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4193_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4193) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) (safeRuntime_block_4193_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4193_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4193_fallthrough`. -/
def safeRuntime_block_4193_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4193. -/
theorem safeRuntime_block_4193_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4193) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) (safeRuntime_block_4193_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4200)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4193_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4193) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) (safeRuntime_block_4193_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4193_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4200. -/
theorem safeRuntime_block_4200_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 589)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4200_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4200_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4200. -/
theorem safeRuntime_block_4200_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4212)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4200_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4200) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4200_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4212_taken`. -/
def safeRuntime_block_4212_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4212. -/
theorem safeRuntime_block_4212_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 3913) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 3913) (safeRuntime_block_4212_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.gt (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 3913) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3913)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4212_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 3913) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 3913) (safeRuntime_block_4212_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4212_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4212_fallthrough`. -/
def safeRuntime_block_4212_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4212. -/
theorem safeRuntime_block_4212_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4229) (safeRuntime_block_4212_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.gt (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 3913) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4229)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4212_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4212) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4229) (safeRuntime_block_4212_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4212_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4229`. -/
def safeRuntime_block_4229_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 4242) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4229. -/
theorem safeRuntime_block_4229 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7083) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4229) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (safeRuntime_block_4229_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4242) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.calldatasize (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7083) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7083)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4229_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7083) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4229) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (safeRuntime_block_4229_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4229 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4242_taken`. -/
def safeRuntime_block_4242_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4242. -/
theorem safeRuntime_block_4242_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 3913) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4242) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 3913) (safeRuntime_block_4242_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 14) (C + ((45))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.gt (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3913) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3913)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4242_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 3913) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4242) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 3913) (safeRuntime_block_4242_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4242_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4242_fallthrough`. -/
def safeRuntime_block_4242_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4242. -/
theorem safeRuntime_block_4242_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4242) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4262) (safeRuntime_block_4242_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 14) (C + ((45))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.gt (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3913) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4262)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4242_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4242) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4262) (safeRuntime_block_4242_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4242_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4262`. -/
def safeRuntime_block_4262_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 4278) :: (UInt256.ofNat 970) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4262. -/
theorem safeRuntime_block_4262 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7262) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4262) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7262) (safeRuntime_block_4262_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4278) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 970) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7262) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7262)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4262_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7262) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4262) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7262) (safeRuntime_block_4262_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4262 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4278`. -/
def safeRuntime_block_4278_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4278. -/
theorem safeRuntime_block_4278 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9258) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4278) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9258) (safeRuntime_block_4278_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 9258) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9258)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4278_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9258) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4278) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9258) (safeRuntime_block_4278_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4278 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4287_taken`. -/
def safeRuntime_block_4287_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4287. -/
theorem safeRuntime_block_4287_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4287) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) (safeRuntime_block_4287_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 589)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4287_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4287) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) (safeRuntime_block_4287_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4287_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4287_fallthrough`. -/
def safeRuntime_block_4287_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4287. -/
theorem safeRuntime_block_4287_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4287) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) (safeRuntime_block_4287_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4294)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4287_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4287) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) (safeRuntime_block_4287_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4287_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4294. -/
theorem safeRuntime_block_4294_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 589)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4294_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 589) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 589) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4294_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4294. -/
theorem safeRuntime_block_4294_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4306) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 589) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4306)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4294_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4294) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4306) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4294_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4306`. -/
def safeRuntime_block_4306_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4327) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x0 :: (UInt256.ofNat 64) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4306. -/
theorem safeRuntime_block_4306 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6952) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4306) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (safeRuntime_block_4306_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 4327) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 6952) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6952)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4306_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6952) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4306) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (safeRuntime_block_4306_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4306 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4327. -/
theorem safeRuntime_block_4327 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4327) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.Safe.ViaIR.safeBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x2 x3 ((keccakWord x2 x3 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32) x2.toNat 32) x4.toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord x2 x3 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32) x2.toNat 32) x4.toNat 32) (memLoad (UInt256.ofNat 64) ((keccakWord x2 x3 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32) x2.toNat 32) x4.toNat 32)).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) ((keccakWord x2 x3 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.land x0 x1).toByteArray.write 0 mem x2.toNat 32) x4.toNat 32) x2.toNat 32) x4.toNat 32)).toNat x4.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r12 := r11.calldataload (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup4 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  exact RD.genRet r23 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_4354_taken`. -/
def safeRuntime_block_4354_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4354. -/
theorem safeRuntime_block_4354_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 320)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4354) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4354_taken_stack (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4354_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 320)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4354) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4354_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4354_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.ViaIR.RuntimeBlocks
