import Reasoning.Reach
import Benchmarks.Safe.V2_0e91d99.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 8168. -/
theorem safeRuntime_block_8168_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8310) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8310) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8310) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8310)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8168_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8310) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8310) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8168_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8168. -/
theorem safeRuntime_block_8168_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8310) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8177)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8168_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8168_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8177_taken`. -/
def safeRuntime_block_8177_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x4 :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8177. -/
theorem safeRuntime_block_8177_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x4 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8195) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (safeRuntime_block_8177_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M aw x4 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((33) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8195) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8195)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8177_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x4 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8195) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (safeRuntime_block_8177_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8177_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8177_fallthrough`. -/
def safeRuntime_block_8177_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x4 :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8177. -/
theorem safeRuntime_block_8177_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x4 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8188) (safeRuntime_block_8177_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M aw x4 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((33) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8195) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8188)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8177_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x4 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8177) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8188) (safeRuntime_block_8177_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8177_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8188`. -/
def safeRuntime_block_8188_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 8195) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8188. -/
theorem safeRuntime_block_8188 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11368) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8188) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11368) (safeRuntime_block_8188_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8195) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11368) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11368)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8188_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11368) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8188) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11368) (safeRuntime_block_8188_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8188 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8195_taken`. -/
def safeRuntime_block_8195_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem) :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8195. -/
theorem safeRuntime_block_8195_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8247) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8247) (safeRuntime_block_8195_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 26) (C + ((84) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.mul (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 8247) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8247)) r26 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8195_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8247) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8247) (safeRuntime_block_8195_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8195_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8195_fallthrough`. -/
def safeRuntime_block_8195_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem) :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8195. -/
theorem safeRuntime_block_8195_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8231) (safeRuntime_block_8195_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 26) (C + ((84) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.mul (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 8247) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8231)) r26 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8195_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8195) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8231) (safeRuntime_block_8195_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8195_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8231`. -/
def safeRuntime_block_8231_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 76584619021) (UInt256.ofNat 218)) :: (UInt256.ofNat 8247) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8231. -/
theorem safeRuntime_block_8231 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8231) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8231_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8247) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 76584619021) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 218) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8231_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8231) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8231_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8231 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8247`. -/
def safeRuntime_block_8247_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 8256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8247. -/
theorem safeRuntime_block_8247 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6783) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8247) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6783) (safeRuntime_block_8247_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8256) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6783) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6783)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8247_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6783) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8247) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6783) (safeRuntime_block_8247_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8247 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8256`. -/
def safeRuntime_block_8256_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x1) :: x2 :: x0 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_8256`. -/
def safeRuntime_block_8256_memory {mem : ByteArray} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8256. -/
theorem safeRuntime_block_8256 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8168) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8256) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (safeRuntime_block_8256_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_8256_memory (mem := mem) (x3 := x3)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.swap4 (by native_decide) (by evm_ov)
  have r8 := r7.dup5 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sload r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.sub (by native_decide) (by evm_ov)
  have r27 := r26.not (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.swap5 (by native_decide) (by evm_ov)
  have r30 := r29.dup3 (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.swap5 (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.swap5 (by native_decide) (by evm_ov)
  have r35 := r34.or (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := r36.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r38⟩ := RD.sstore r37 hperm (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 8168) (by native_decide) (by evm_ov)
  have r42 := r41.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8168)) r42 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8256_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8168) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8256) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8168) (safeRuntime_block_8256_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_8256_memory (mem := mem) (x3 := x3)) aw' rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8256 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8310`. -/
def safeRuntime_block_8310_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `safeRuntime_block_8310`. -/
def safeRuntime_block_8310_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8310. -/
theorem safeRuntime_block_8310 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x5 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8310) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x5 (safeRuntime_block_8310_stack (R := R)) (safeRuntime_block_8310_memory (mem := mem) (x2 := x2)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (UInt256.ofNat 3) x1) (UInt256.ofNat 4) x3) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := RD.genKeccak256 r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r26 := r25.shl (by native_decide) (by evm_ov)
  have r27 := r26.sub (by native_decide) (by evm_ov)
  have r28 := r27.not (by native_decide) (by evm_ov)
  have r29 := r28.and (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.or (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sstore r32 hperm (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r35⟩ := RD.sstore r34 hperm (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r37⟩ := RD.sstore r36 hperm (by native_decide) (by evm_ov)
  have r38 := r37.pop (by native_decide) (by evm_ov)
  have r39 := r38.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r39⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8310_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x5 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8310) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x5 (safeRuntime_block_8310_stack (R := R)) (safeRuntime_block_8310_memory (mem := mem) (x2 := x2)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (UInt256.ofNat 3) x1) (UInt256.ofNat 4) x3) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8310 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8361. -/
theorem safeRuntime_block_8361_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.codeOwner.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8394) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8361) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8394) (x0 :: R) mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.address (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8394) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8394)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8361_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.codeOwner.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8394) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8361) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8394) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8361_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8361. -/
theorem safeRuntime_block_8361_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.codeOwner.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8361) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8378) (x0 :: R) mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.address (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8394) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8378)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8361_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.codeOwner.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8361) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8378) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8361_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8378`. -/
def safeRuntime_block_8378_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 19146162947) (UInt256.ofNat 220)) :: (UInt256.ofNat 8394) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8378. -/
theorem safeRuntime_block_8378 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8378) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8378_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8394) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 19146162947) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8378_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8378) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8378_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8378 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8394`. -/
def safeRuntime_block_8394_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8394. -/
theorem safeRuntime_block_8394 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8394) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x1 (safeRuntime_block_8394_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r4⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8394_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8394) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x1 (safeRuntime_block_8394_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8394 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8430_taken`. -/
def safeRuntime_block_8430_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8430. -/
theorem safeRuntime_block_8430_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8504) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8430) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) R (safeRuntime_block_8430_taken_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8504) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8504)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8430_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8504) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8430) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) R (safeRuntime_block_8430_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8430_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8430_fallthrough`. -/
def safeRuntime_block_8430_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8430. -/
theorem safeRuntime_block_8430_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8430) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8488) R (safeRuntime_block_8430_fallthrough_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8504) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8488)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8430_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8430) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8488) R (safeRuntime_block_8430_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8430_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8488`. -/
def safeRuntime_block_8488_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 19146150659) (UInt256.ofNat 220)) :: (UInt256.ofNat 8504) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8488. -/
theorem safeRuntime_block_8488 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8488) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8488_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8504) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 19146150659) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8488_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8488) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8488_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8488 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8504_taken`. -/
def safeRuntime_block_8504_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8504. -/
theorem safeRuntime_block_8504_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (x0 :: x1 :: R) (safeRuntime_block_8504_taken_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.not (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  have r23 := r22.or (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sstore r24 hperm (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.iszero (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r35 := r34.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1936)) r35 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8504_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (x0 :: x1 :: R) (safeRuntime_block_8504_taken_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8504_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8504_fallthrough`. -/
def safeRuntime_block_8504_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8504. -/
theorem safeRuntime_block_8504_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) (safeRuntime_block_8504_fallthrough_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.not (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  have r23 := r22.or (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sstore r24 hperm (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.iszero (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r35 := r34.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8581)) r35 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8504_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8504) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) (safeRuntime_block_8504_fallthrough_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8504_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V2_0e91d99.RuntimeBlocks
