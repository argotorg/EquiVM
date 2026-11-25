import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Automatically generated RD summary for bytecode block at pc 22436. -/
theorem midnight_block_22436_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 15552000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22570) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 15552000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22570) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22570)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22436_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 15552000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22570) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22436_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22436. -/
theorem midnight_block_22436_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 15552000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 15552000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22570) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22448)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22436_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 15552000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22436) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22436_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22448_taken`. -/
def midnight_block_22448_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22448. -/
theorem midnight_block_22448_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22448_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
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
theorem midnight_block_22448_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22448_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22448_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22448_fallthrough`. -/
def midnight_block_22448_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22448. -/
theorem midnight_block_22448_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (midnight_block_22448_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22484)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22448_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 64)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22448) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (midnight_block_22448_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22448_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22484_taken`. -/
def midnight_block_22484_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22484. -/
theorem midnight_block_22484_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22484_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
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
theorem midnight_block_22484_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22484_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22484_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22484_fallthrough`. -/
def midnight_block_22484_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22484. -/
theorem midnight_block_22484_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22520) (midnight_block_22484_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22520)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22484_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22484) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22520) (midnight_block_22484_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22484_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22520`. -/
def midnight_block_22520_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 7776000) :: (UInt256.ofNat 16777215) :: (UInt256.ofNat 22009) :: x0 :: (UInt256.ofNat 7530) :: (UInt256.ofNat 15552000) :: (UInt256.ofNat 22015) :: x2 :: (UInt256.ofNat 22021) :: (UInt256.ofNat 4294967295) :: (UInt256.ofNat 22027) :: x1 :: (UInt256.ofNat 22033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22520. -/
theorem midnight_block_22520 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22520) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (midnight_block_22520_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 16) (C + ((48))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22033) (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 22015) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22027) (by native_decide) (by evm_ov)
  have r7 := r6.swap5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7530) (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 7776000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.swap8 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 22009) (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 15552000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.swap5 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.swap11 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22561)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22520_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22520) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (midnight_block_22520_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22520 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22561`. -/
def midnight_block_22561_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x5 :: x4 :: x11 :: x6 :: x7 :: x8 :: x9 :: x10 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22561. -/
theorem midnight_block_22561 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22427) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (midnight_block_22561_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.swap11 (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22427) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22427)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22561_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22427) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22427) (midnight_block_22561_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22561 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22570_taken`. -/
def midnight_block_22570_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22570. -/
theorem midnight_block_22570_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22570_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 22) (C + ((75))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22570_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22570_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22570_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22570_fallthrough`. -/
def midnight_block_22570_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22570. -/
theorem midnight_block_22570_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (midnight_block_22570_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 22) (C + ((75))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22607)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22570_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 80)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22570) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (midnight_block_22570_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22570_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22607_taken`. -/
def midnight_block_22607_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22607. -/
theorem midnight_block_22607_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22607_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
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
theorem midnight_block_22607_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22607_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22607_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22607_fallthrough`. -/
def midnight_block_22607_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22607. -/
theorem midnight_block_22607_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22643) (midnight_block_22607_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 21) (C + ((74))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22643)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22607_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22607) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22643) (midnight_block_22607_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22607_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22643`. -/
def midnight_block_22643_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 15552000) :: (UInt256.ofNat 16777215) :: (UInt256.ofNat 22009) :: x0 :: (UInt256.ofNat 7530) :: (UInt256.ofNat 31104000) :: (UInt256.ofNat 22015) :: x2 :: (UInt256.ofNat 22021) :: (UInt256.ofNat 4294967295) :: (UInt256.ofNat 22027) :: x1 :: (UInt256.ofNat 22033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22643. -/
theorem midnight_block_22643 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22561) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22643) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (midnight_block_22643_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 18) (C + ((59))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22033) (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 22015) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 22027) (by native_decide) (by evm_ov)
  have r7 := r6.swap5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7530) (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 15552000) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.swap8 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 22009) (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 31104000) (by native_decide) (by evm_ov)
  have r14 := r13.swap5 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.swap11 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 22561) (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22561)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22643_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22561) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22643) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22561) (midnight_block_22643_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22643 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22689_taken`. -/
def midnight_block_22689_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22689. -/
theorem midnight_block_22689_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22689_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 22) (C + ((74))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22689_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_22689_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22689_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22689_fallthrough`. -/
def midnight_block_22689_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22689. -/
theorem midnight_block_22689_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22726) (midnight_block_22689_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 22) (C + ((74))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22726)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22689_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535))) (UInt256.eq (UInt256.ofNat 1000000000000) (UInt256.div (UInt256.mul (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)) (UInt256.ofNat 1000000000000)) (UInt256.land (UInt256.shiftRight x0 (UInt256.ofNat 96)) (UInt256.ofNat 65535)))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22726) (midnight_block_22689_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22689_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22726`. -/
def midnight_block_22726_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22726. -/
theorem midnight_block_22726 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22726) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_22726_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r2 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22726_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22726) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_22726_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22726 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22728. -/
theorem midnight_block_22728_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22770) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22728) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22770) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 22770) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22770)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22728_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 22770) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22728) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22770) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22728_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 22728. -/
theorem midnight_block_22728_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22728) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22735) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 22770) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22735)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22728_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22728) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22735) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22728_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22735`. -/
def midnight_block_22735_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (UInt256.ofNat 22745) :: x0 :: (UInt256.ofNat rdata.size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22735. -/
theorem midnight_block_22735 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19016) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22735) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19016) (midnight_block_22735_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22745) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19016) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19016)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22735_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19016) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22735) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19016) (midnight_block_22735_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22735 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_22745`. -/
def midnight_block_22745_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.ofNat 22759) :: x2 :: x1 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22745. -/
theorem midnight_block_22745 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22745) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_22745_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 22759) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.swap4 (by native_decide) (by evm_ov)
  have r7 := r6.dup5 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_22745_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22745) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_22745_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_22745 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
