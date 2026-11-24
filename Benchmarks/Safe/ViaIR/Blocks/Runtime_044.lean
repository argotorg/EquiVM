import Reasoning.Reach
import Benchmarks.Safe.ViaIR.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR.RuntimeBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `safeRuntime_block_9474_fallthrough`. -/
def safeRuntime_block_9474_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.mul x1 x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9474. -/
theorem safeRuntime_block_9474_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.div (UInt256.mul x1 x0) x1)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9474) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9487) (safeRuntime_block_9474_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((44))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.mul (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.div (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7511) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9487)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9474_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.div (UInt256.mul x1 x0) x1)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9474) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9487) (safeRuntime_block_9474_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9474_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9487`. -/
def safeRuntime_block_9487_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: (UInt256.ofNat 9453) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9487. -/
theorem safeRuntime_block_9487 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 8870) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9487) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 8870) (safeRuntime_block_9487_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 9453) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8870) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8870)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9487_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 8870) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9487) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 8870) (safeRuntime_block_9487_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9487 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9496`. -/
def safeRuntime_block_9496_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9496. -/
theorem safeRuntime_block_9496 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9496) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x2 (safeRuntime_block_9496_stack (R := R)) mem aw rdata σ (k + 6) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9496_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9496) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x2 (safeRuntime_block_9496_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9496 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9502. -/
theorem safeRuntime_block_9502 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9502) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 306338476081) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9547. -/
theorem safeRuntime_block_9547 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9547) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 153169238041) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 217) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9592. -/
theorem safeRuntime_block_9592 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9592) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 306338410545) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9637. -/
theorem safeRuntime_block_9637 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9637) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 76584619021) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 218) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9682. -/
theorem safeRuntime_block_9682 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9682) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 306338345521) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9727. -/
theorem safeRuntime_block_9727 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9727) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 153169172633) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 217) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 9772. -/
theorem safeRuntime_block_9772 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9772) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.ViaIR.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 306338345265) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 216) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  exact RD.genRev r27 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9817_taken`. -/
def safeRuntime_block_9817_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val)) :: x1 :: x3 :: x2 :: x4 :: (⟨0⟩ : UInt256) :: x0 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9817. -/
theorem safeRuntime_block_9817_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 10109) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9817) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 10109) (safeRuntime_block_9817_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.swap4 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.swap4 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.caller (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.eq (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 10109) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10109)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9817_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 10109) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9817) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 10109) (safeRuntime_block_9817_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_9817_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9817_fallthrough`. -/
def safeRuntime_block_9817_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val)) :: x1 :: x3 :: x2 :: x4 :: (⟨0⟩ : UInt256) :: x0 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9817. -/
theorem safeRuntime_block_9817_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9817) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (safeRuntime_block_9817_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 80067992571439485785405894129641280630172609254213753706009264638304931322183) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.swap4 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.swap4 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.caller (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.eq (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 10109) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9869)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9817_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat ee.source.val))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9817) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (safeRuntime_block_9817_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_9817_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9869_taken`. -/
def safeRuntime_block_9869_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 9869. -/
theorem safeRuntime_block_9869_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 10064) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 10064) (safeRuntime_block_9869_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10064) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10064)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9869_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 10064) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 10064) (safeRuntime_block_9869_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9869_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9869_fallthrough`. -/
def safeRuntime_block_9869_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 9869. -/
theorem safeRuntime_block_9869_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (safeRuntime_block_9869_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10064) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9874)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9869_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9869) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (safeRuntime_block_9869_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9869_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9874_taken`. -/
def safeRuntime_block_9874_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9874. -/
theorem safeRuntime_block_9874_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9899) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9899) (safeRuntime_block_9874_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.dup8 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9899) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9899)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9874_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9899) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9899) (safeRuntime_block_9874_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9874_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9874_fallthrough`. -/
def safeRuntime_block_9874_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9874. -/
theorem safeRuntime_block_9874_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9890) (safeRuntime_block_9874_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.dup8 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9899) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9890)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9874_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9874) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9890) (safeRuntime_block_9874_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9874_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9890`. -/
def safeRuntime_block_9890_stack {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9890. -/
theorem safeRuntime_block_9890 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9890) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x4 (safeRuntime_block_9890_stack (x5 := x5) (R := R)) mem aw rdata σ (k + 9) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9890_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9890) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x4 (safeRuntime_block_9890_stack (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9890 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9899`. -/
def safeRuntime_block_9899_stack {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 164)) :: (UInt256.ofNat 9968) :: (UInt256.ofNat 9979) :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: x2 :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 32) :: (memLoad (UInt256.ofNat 64) mem) :: x4 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9899`. -/
def safeRuntime_block_9899_memory {mem : ByteArray} {x1 : UInt256} {x6 : UInt256} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x6).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 960894137) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9899. -/
theorem safeRuntime_block_9899 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7374) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9899) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7374) (safeRuntime_block_9899_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_9899_memory (mem := mem) (x1 := x1) (x6 := x6)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 49) (C + ((148) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9968) (by native_decide) (by evm_ov)
  have r3 := r2.swap6 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap5 (by native_decide) (by evm_ov)
  have r7 := r6.swap7 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9979) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap9 (by native_decide) (by evm_ov)
  have r14 := r13.dup10 (by native_decide) (by evm_ov)
  have r15 := r14.swap8 (by native_decide) (by evm_ov)
  have r16 := r15.dup9 (by native_decide) (by evm_ov)
  have r17 := r16.swap7 (by native_decide) (by evm_ov)
  have r18 := r17.dup8 (by native_decide) (by evm_ov)
  have r19 := r18.swap6 (by native_decide) (by evm_ov)
  have r20 := r19.push4 (UInt256.ofNat 960894137) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r22 := r21.shl (by native_decide) (by evm_ov)
  have r23 := r22.dup8 (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r28 := r27.shl (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r32 := r31.dup8 (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := RD.genMstore r33 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r36 := r35.dup7 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r41 := r40.dup7 (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r45 := r44.dup6 (by native_decide) (by evm_ov)
  have r46 := r45.add (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 7374) (by native_decide) (by evm_ov)
  have r49 := r48.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7374)) r49 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9899_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7374) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9899) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7374) (safeRuntime_block_9899_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_9899_memory (mem := mem) (x1 := x1) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9899 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9968`. -/
def safeRuntime_block_9968_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (x3 + (UInt256.ofNat 100)) :: x1 :: x0 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9968. -/
theorem safeRuntime_block_9968 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 8837) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9968) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 8837) (safeRuntime_block_9968_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8837) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8837)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9968_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 8837) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9968) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 8837) (safeRuntime_block_9968_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9968 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9979`. -/
def safeRuntime_block_9979_stack {g : Sat256} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((21) + (memExpansionCost aw (x1 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x4 :: x2 :: x3 :: (UInt256.sub x0 x1) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9979`. -/
def safeRuntime_block_9979_memory {ee : ExecutionEnv} {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (x1 + (UInt256.ofNat 132)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9979. -/
theorem safeRuntime_block_9979 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9979) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9989) (safeRuntime_block_9979_stack (g := g) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_9979_memory (ee := ee) (mem := mem) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((23) + (memExpansionCost aw (x1 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := RD.genGas (RD.normalizeCounters (k' := k + 8) (C' := C + ((21) + (memExpansionCost aw (x1 + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)))) r8 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9989)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9979_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9979) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9989) (safeRuntime_block_9979_stack (g := g) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_9979_memory (ee := ee) (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9979 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 9989: call (0xf1). No RD transition is asserted. Summaries resume at pc 9990 from a fresh symbolic RD state. -/

end Benchmarks.Safe.ViaIR.RuntimeBlocks
