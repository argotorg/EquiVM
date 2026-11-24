import Reasoning.Reach
import Benchmarks.Safe.V2_0e91d99.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 8581. -/
theorem safeRuntime_block_8581_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (extCodeSizeWord σ x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8603) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8603) (x0 :: x1 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := r1.extcodesize (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8603) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8603)) r4 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8581_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (extCodeSizeWord σ x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8603) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8603) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8581_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8581. -/
theorem safeRuntime_block_8581_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (extCodeSizeWord σ x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8587) (x0 :: x1 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := r1.extcodesize (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8603) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8587)) r4 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8581_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (extCodeSizeWord σ x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8587) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8581_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8587`. -/
def safeRuntime_block_8587_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 153169172505) (UInt256.ofNat 217)) :: (UInt256.ofNat 8603) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8587. -/
theorem safeRuntime_block_8587 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8587) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8587_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8603) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 153169172505) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 217) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8587_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8587) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8587_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8587 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8603`. -/
def safeRuntime_block_8603_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.lnot (⟨0⟩ : UInt256)) :: (UInt256.ofNat 1) :: x0 :: (⟨0⟩ : UInt256) :: x1 :: (UInt256.ofNat 8618) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8603. -/
theorem safeRuntime_block_8603 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7519) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8603) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7519) (safeRuntime_block_8603_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8618) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 7519) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7519)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8603_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 7519) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8603) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 7519) (safeRuntime_block_8603_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8603 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8618_taken`. -/
def safeRuntime_block_8618_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8618. -/
theorem safeRuntime_block_8618_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8618) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (safeRuntime_block_8618_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1936)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8618_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8618) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (safeRuntime_block_8618_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8618_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8618_fallthrough`. -/
def safeRuntime_block_8618_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8618. -/
theorem safeRuntime_block_8618_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8618) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8623) (safeRuntime_block_8618_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8623)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8618_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8618) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8623) (safeRuntime_block_8618_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8618_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8623`. -/
def safeRuntime_block_8623_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 19146146563) (UInt256.ofNat 220)) :: (UInt256.ofNat 1936) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8623. -/
theorem safeRuntime_block_8623 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8623) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8623_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 19146146563) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8623_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8623) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8623_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8623 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8639`. -/
def safeRuntime_block_8639_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 8648) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8639. -/
theorem safeRuntime_block_8639 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8700) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8639) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (safeRuntime_block_8639_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8648) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8700) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8700)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8639_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8700) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8639) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (safeRuntime_block_8639_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8639 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8648_taken`. -/
def safeRuntime_block_8648_taken_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8648. -/
theorem safeRuntime_block_8648_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8648) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (x0 :: x1 :: R) (safeRuntime_block_8648_taken_memory (mem := mem) (x1 := x1)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
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
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.eq (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r28 := r27.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1936)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8648_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8648) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 1936) (x0 :: x1 :: R) (safeRuntime_block_8648_taken_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8648_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8648_fallthrough`. -/
def safeRuntime_block_8648_fallthrough_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8648. -/
theorem safeRuntime_block_8648_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8648) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8684) (x0 :: x1 :: R) (safeRuntime_block_8648_fallthrough_memory (mem := mem) (x1 := x1)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
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
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.eq (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r28 := r27.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8684)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8648_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8648) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8684) (x0 :: x1 :: R) (safeRuntime_block_8648_fallthrough_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8648_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8684`. -/
def safeRuntime_block_8684_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 306338476085) (UInt256.ofNat 216)) :: (UInt256.ofNat 1936) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8684. -/
theorem safeRuntime_block_8684 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8684) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8684_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 306338476085) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8684_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8684) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_8684_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8684 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8700_taken`. -/
def safeRuntime_block_8700_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8700. -/
theorem safeRuntime_block_8700_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8731) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (safeRuntime_block_8700_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8731) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8731)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8700_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8731) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (safeRuntime_block_8700_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8700_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8700_fallthrough`. -/
def safeRuntime_block_8700_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8700. -/
theorem safeRuntime_block_8700_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8717) (safeRuntime_block_8700_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8731) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8717)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8700_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8700) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8717) (safeRuntime_block_8700_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8700_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8717`. -/
def safeRuntime_block_8717_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8717. -/
theorem safeRuntime_block_8717 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8717) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (safeRuntime_block_8717_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((29))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.eq (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8731)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8717_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8717) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (safeRuntime_block_8717_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8717 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8731. -/
theorem safeRuntime_block_8731_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8766) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8766) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8766)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8731_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8766) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8731_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8731. -/
theorem safeRuntime_block_8731_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8766) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8737)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8731_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8731) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8731_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8737_taken`. -/
def safeRuntime_block_8737_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8737. -/
theorem safeRuntime_block_8737_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8766) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (safeRuntime_block_8737_taken_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.address (by native_decide) (by evm_ov)
  have r10 := r9.eq (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 8766) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8766)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8737_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8766) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (safeRuntime_block_8737_taken_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8737_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8737_fallthrough`. -/
def safeRuntime_block_8737_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8737. -/
theorem safeRuntime_block_8737_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8756) (safeRuntime_block_8737_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.address (by native_decide) (by evm_ov)
  have r10 := r9.eq (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 8766) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8756)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8737_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8737) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8756) (safeRuntime_block_8737_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8737_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8756`. -/
def safeRuntime_block_8756_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 8764) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8756. -/
theorem safeRuntime_block_8756 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8928) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8756) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8928) (safeRuntime_block_8756_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8764) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8928) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8928)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8756_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8928) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8756) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8928) (safeRuntime_block_8756_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8756 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8764`. -/
def safeRuntime_block_8764_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8764. -/
theorem safeRuntime_block_8764 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8764) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (safeRuntime_block_8764_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8766)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8764_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8764) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8766) (safeRuntime_block_8764_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8764 hstack h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V2_0e91d99.RuntimeBlocks
