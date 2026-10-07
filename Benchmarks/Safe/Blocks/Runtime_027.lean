import Reasoning.Reach
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeRuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_5710`. -/
def safeRuntime_block_5710_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5710. -/
theorem safeRuntime_block_5710 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5710) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x5 (safeRuntime_block_5710_stack (R := R)) mem (M aw x1 x0) rdata σ (k + 6) (C + ((18) + (memExpansionCost aw x1 x0) + (375 + 8 * x0.toNat + 2 * 375))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 77212943334077718225880146371662869374096224703205130304566303938038540354166) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := RD.genLog2 r2 (by native_decide) hperm (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5710_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5710) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x5 (safeRuntime_block_5710_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5710 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5748`. -/
def safeRuntime_block_5748_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5756) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5748. -/
theorem safeRuntime_block_5748 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5748) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_5748_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5756) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6757) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6757)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5748_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5748) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_5748_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5748 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5756_taken`. -/
def safeRuntime_block_5756_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5756. -/
theorem safeRuntime_block_5756_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5886) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5756) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (safeRuntime_block_5756_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
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
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5886) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5886)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5756_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5886) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5756) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (safeRuntime_block_5756_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5756_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5756_fallthrough`. -/
def safeRuntime_block_5756_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5756. -/
theorem safeRuntime_block_5756_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5756) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5775) (safeRuntime_block_5756_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
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
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5886) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5775)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5756_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5756) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5775) (safeRuntime_block_5756_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5756_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5775`. -/
def safeRuntime_block_5775_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((104) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 185074651) (UInt256.ofNat 227)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 36) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 185074651) (UInt256.ofNat 227)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 185074651) (UInt256.ofNat 227)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 36) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 33540519) :: (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5775`. -/
def safeRuntime_block_5775_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 185074651) (UInt256.ofNat 227)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5775. -/
theorem safeRuntime_block_5775 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5833) (safeRuntime_block_5775_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (R := R)) (safeRuntime_block_5775_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 36) (C + ((106) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 33540519) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 185074651) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 227) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.push4 (UInt256.ofNat 33540519) (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r27 := r26.add (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.dup1 (by native_decide) (by evm_ov)
  have r32 := r31.dup4 (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.dup7 (by native_decide) (by evm_ov)
  have r36 := RD.genGas (RD.normalizeCounters (k' := k + 35) (C' := C + ((104) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r35 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5833)) r36 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5775_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5833) (safeRuntime_block_5775_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (R := R)) (safeRuntime_block_5775_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5775 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 5833: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 5834 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_5834_taken`. -/
def safeRuntime_block_5834_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5834. -/
theorem safeRuntime_block_5834_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5848) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5834) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5848) (safeRuntime_block_5834_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5848) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5848)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5834_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5848) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5834) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5848) (safeRuntime_block_5834_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5834_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5834_fallthrough`. -/
def safeRuntime_block_5834_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5834. -/
theorem safeRuntime_block_5834_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5834) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5841) (safeRuntime_block_5834_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5848) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5841)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5834_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5834) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5841) (safeRuntime_block_5834_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5834_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5841. -/
theorem safeRuntime_block_5841 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5841) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
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

/-- Final stack for bytecode block summary `safeRuntime_block_5848`. -/
def safeRuntime_block_5848_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 5884) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5848`. -/
def safeRuntime_block_5848_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5848. -/
theorem safeRuntime_block_5848 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11632) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5848) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11632) (safeRuntime_block_5848_stack (mem := mem) (rdata := rdata) (R := R)) (safeRuntime_block_5848_memory (mem := mem) (rdata := rdata)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r10 := r9.not (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 5884) (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 11632) (by native_decide) (by evm_ov)
  have r28 := r27.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11632)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5848_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11632) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5848) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11632) (safeRuntime_block_5848_stack (mem := mem) (rdata := rdata) (R := R)) (safeRuntime_block_5848_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5848 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5884`. -/
def safeRuntime_block_5884_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5884. -/
theorem safeRuntime_block_5884 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5884) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (safeRuntime_block_5884_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5886)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5884_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5884) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (safeRuntime_block_5884_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5884 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5886_taken`. -/
def safeRuntime_block_5886_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5886. -/
theorem safeRuntime_block_5886_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5908) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5908) (safeRuntime_block_5886_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5908) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5908)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5886_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 5908) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5908) (safeRuntime_block_5886_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5886_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5886_fallthrough`. -/
def safeRuntime_block_5886_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5886. -/
theorem safeRuntime_block_5886_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5892) (safeRuntime_block_5886_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5908) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5892)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5886_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5886) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5892) (safeRuntime_block_5886_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5886_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5892`. -/
def safeRuntime_block_5892_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 306338541617) (UInt256.ofNat 216)) :: (UInt256.ofNat 5908) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5892. -/
theorem safeRuntime_block_5892 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5892) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_5892_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5908) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 306338541617) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5892_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5892) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_5892_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5892 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5908`. -/
def safeRuntime_block_5908_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5908. -/
theorem safeRuntime_block_5908 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5908) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x1 (safeRuntime_block_5908_stack (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.pushConst (UInt256.ofNat 92769014903763716504357727009264453482757621201785749170460437511245192399800) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := RD.genLog2 r19 (by native_decide) hperm (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r22⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5908_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5908) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x1 (safeRuntime_block_5908_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5908 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5998`. -/
def safeRuntime_block_5998_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 6006) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5998. -/
theorem safeRuntime_block_5998 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5998) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_5998_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6006) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6757) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6757)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5998_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 5998) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_5998_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5998 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6006_taken`. -/
def safeRuntime_block_6006_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6006. -/
theorem safeRuntime_block_6006_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6136) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6006) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6136) (safeRuntime_block_6006_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
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
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6136) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6136)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6006_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6136) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6006) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6136) (safeRuntime_block_6006_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6006_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6006_fallthrough`. -/
def safeRuntime_block_6006_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6006. -/
theorem safeRuntime_block_6006_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6006) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6025) (safeRuntime_block_6006_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
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
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6136) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6025)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6006_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6006) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6025) (safeRuntime_block_6006_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6006_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6025`. -/
def safeRuntime_block_6025_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((104) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1936446493) (UInt256.ofNat 225)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 36) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1936446493) (UInt256.ofNat 225)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1936446493) (UInt256.ofNat 225)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 36) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 33540519) :: (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_6025`. -/
def safeRuntime_block_6025_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1936446493) (UInt256.ofNat 225)).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 33540519) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6025. -/
theorem safeRuntime_block_6025 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6025) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6083) (safeRuntime_block_6025_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (R := R)) (safeRuntime_block_6025_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 36) (C + ((106) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 33540519) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1936446493) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.push4 (UInt256.ofNat 33540519) (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r27 := r26.add (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.dup1 (by native_decide) (by evm_ov)
  have r32 := r31.dup4 (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.dup7 (by native_decide) (by evm_ov)
  have r36 := RD.genGas (RD.normalizeCounters (k' := k + 35) (C' := C + ((104) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r35 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6083)) r36 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6025_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6025) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6083) (safeRuntime_block_6025_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (R := R)) (safeRuntime_block_6025_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6025 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 6083: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 6084 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_6084_taken`. -/
def safeRuntime_block_6084_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6084. -/
theorem safeRuntime_block_6084_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6098) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6084) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6098) (safeRuntime_block_6084_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6098) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6098)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6084_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6098) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6084) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6098) (safeRuntime_block_6084_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6084_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6084_fallthrough`. -/
def safeRuntime_block_6084_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6084. -/
theorem safeRuntime_block_6084_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6084) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6091) (safeRuntime_block_6084_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6098) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6091)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6084_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6084) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6091) (safeRuntime_block_6084_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6084_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end safeRuntimeBlocks
