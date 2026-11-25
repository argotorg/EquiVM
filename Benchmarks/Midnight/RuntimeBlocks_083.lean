import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_22084_taken`. -/
def midnight_block_22084_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22084. -/
theorem midnight_block_22084_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22084_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22084_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22084_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22084_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22084_fallthrough`. -/
def midnight_block_22084_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22084. -/
theorem midnight_block_22084_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22120) (midnight_block_22084_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22120)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22084_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22120) (midnight_block_22084_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22084_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22120`. -/
def midnight_block_22120_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 86400) :: (UInt256.ofNat 16777215) :: (UInt256.ofNat 22009) :: x0 :: (UInt256.ofNat 7530) :: (UInt256.ofNat 604800) :: (UInt256.ofNat 22015) :: x2 :: (UInt256.ofNat 22021) :: (UInt256.ofNat 4294967295) :: (UInt256.ofNat 22027) :: x1 :: (UInt256.ofNat 22033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22120. -/
theorem midnight_block_22120 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22120) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (midnight_block_22120_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 16) (C + ((48))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22033) (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 22015) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22027) (by native_decide) (by evm_ov)
  have r7 := r6.swap5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7530) (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 86400) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.swap8 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 22009) (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 604800) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.swap5 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.swap11 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22161)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22120_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22120) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (midnight_block_22120_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22120 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22161`. -/
def midnight_block_22161_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x5 :: x4 :: x11 :: x6 :: x7 :: x8 :: x9 :: x10 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22161. -/
theorem midnight_block_22161 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21993) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21993) (midnight_block_22161_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.swap11 (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21993) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21993)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22161_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21993) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21993) (midnight_block_22161_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22161 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22170. -/
theorem midnight_block_22170_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 2592000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 2592000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22302) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22302)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22170_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 2592000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22170_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22170. -/
theorem midnight_block_22170_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 2592000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 2592000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22302) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22182)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22170_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 2592000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22170_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22182_taken`. -/
def midnight_block_22182_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22182. -/
theorem midnight_block_22182_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22182_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22182_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22182_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22182_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22182_fallthrough`. -/
def midnight_block_22182_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22182. -/
theorem midnight_block_22182_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (midnight_block_22182_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22218)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22182_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 32)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22182) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (midnight_block_22182_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22182_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22218_taken`. -/
def midnight_block_22218_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22218. -/
theorem midnight_block_22218_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22218_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 20) (C + ((71))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.mul (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.div (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.eq (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.or (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22218_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22218_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22218_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22218_fallthrough`. -/
def midnight_block_22218_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22218. -/
theorem midnight_block_22218_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22253) (midnight_block_22218_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 20) (C + ((71))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.mul (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.div (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.eq (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.or (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22253)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22218_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22218) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22253) (midnight_block_22218_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22218_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22253`. -/
def midnight_block_22253_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 604800) :: (UInt256.ofNat 16777215) :: (UInt256.ofNat 22009) :: x0 :: (UInt256.ofNat 7530) :: x1 :: (UInt256.ofNat 22015) :: x2 :: (UInt256.ofNat 22021) :: (UInt256.ofNat 4294967295) :: (UInt256.ofNat 22027) :: (UInt256.ofNat 2592000) :: (UInt256.ofNat 22033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22253. -/
theorem midnight_block_22253 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22253) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (midnight_block_22253_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 15) (C + ((45))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22033) (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 22015) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22027) (by native_decide) (by evm_ov)
  have r7 := r6.swap5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7530) (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 604800) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 22009) (by native_decide) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 2592000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.swap11 (by native_decide) (by evm_ov)
  have r14 := r13.swap5 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22293)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22253_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22253) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (midnight_block_22253_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22253 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22293`. -/
def midnight_block_22293_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x5 :: x4 :: x11 :: x6 :: x7 :: x8 :: x9 :: x10 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22293. -/
theorem midnight_block_22293 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22161) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (midnight_block_22293_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap11 (by native_decide) (by evm_ov)
  have r3 := r2.swap5 (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.swap11 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22161) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22161)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22293_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22161) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22161) (midnight_block_22293_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22293 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22302. -/
theorem midnight_block_22302_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7776000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22436) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 7776000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22436) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22436)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22302_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7776000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22436) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22302_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22302. -/
theorem midnight_block_22302_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7776000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 7776000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22436) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22314)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22302_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7776000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22302) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22302_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22314_taken`. -/
def midnight_block_22314_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22314. -/
theorem midnight_block_22314_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22314_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22314_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22314_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22314_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22314_fallthrough`. -/
def midnight_block_22314_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22314. -/
theorem midnight_block_22314_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (midnight_block_22314_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22350)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22314_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 48)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22314) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (midnight_block_22314_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22314_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22350_taken`. -/
def midnight_block_22350_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22350. -/
theorem midnight_block_22350_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22350_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22350_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22350_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22350_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22350_fallthrough`. -/
def midnight_block_22350_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22350. -/
theorem midnight_block_22350_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22386) (midnight_block_22350_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.mul (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.div (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22386)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22350_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22386) (midnight_block_22350_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22350_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22386`. -/
def midnight_block_22386_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2592000) :: (UInt256.ofNat 16777215) :: (UInt256.ofNat 22009) :: (UInt256.ofNat 7776000) :: (UInt256.ofNat 7530) :: x1 :: (UInt256.ofNat 22015) :: x2 :: (UInt256.ofNat 22021) :: (UInt256.ofNat 4294967295) :: (UInt256.ofNat 22027) :: x0 :: (UInt256.ofNat 22033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22386. -/
theorem midnight_block_22386 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22386) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (midnight_block_22386_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 16) (C + ((48))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22033) (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 22015) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22027) (by native_decide) (by evm_ov)
  have r7 := r6.swap5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7530) (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 2592000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 22009) (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 7776000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.swap3 (by native_decide) (by evm_ov)
  have r15 := r14.swap11 (by native_decide) (by evm_ov)
  have r16 := r15.swap5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22427)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22386_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22386) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (midnight_block_22386_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22386 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22427`. -/
def midnight_block_22427_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x5 :: x4 :: x11 :: x6 :: x7 :: x8 :: x9 :: x10 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22427. -/
theorem midnight_block_22427 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22293) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (midnight_block_22427_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap11 (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22293) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22293)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22427_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22293) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22293) (midnight_block_22427_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22427 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
