import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_5254_fallthrough`. -/
def midnight_block_5254_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5254. -/
theorem midnight_block_5254_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5254) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5275) (midnight_block_5254_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap6 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup8 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 8411) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5275)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5254_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5254) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5275) (midnight_block_5254_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_5254_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5275`. -/
def midnight_block_5275_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) + (UInt256.ofNat 228)) :: (UInt256.ofNat 5296) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5275. -/
theorem midnight_block_5275 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19691) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19691) (midnight_block_5275_stack (ee := ee) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5296) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.calldataload (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 19691) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19691)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5275_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19691) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19691) (midnight_block_5275_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5275 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5296_taken`. -/
def midnight_block_5296_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5296. -/
theorem midnight_block_5296_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land x0 x1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 8288) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5296) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 8288) (midnight_block_5296_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8288) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8288)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5296_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land x0 x1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 8288) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5296) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 8288) (midnight_block_5296_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5296_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5296_fallthrough`. -/
def midnight_block_5296_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5296. -/
theorem midnight_block_5296_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land x0 x1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5296) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (midnight_block_5296_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8288) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5305)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5296_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land x0 x1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5296) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (midnight_block_5296_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5296_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5305_taken`. -/
def midnight_block_5305_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5305. -/
theorem midnight_block_5305_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 8267) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 8267) (midnight_block_5305_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8267) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8267)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5305_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 8267) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 8267) (midnight_block_5305_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5305_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5305_fallthrough`. -/
def midnight_block_5305_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5305. -/
theorem midnight_block_5305_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5311) (midnight_block_5305_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8267) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5311)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5305_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5305) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5311) (midnight_block_5305_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5305_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5311`. -/
def midnight_block_5311_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x6 :: x1 :: x0 :: (memLoad (UInt256.ofNat 800) mem) :: (memLoad (UInt256.ofNat 800) mem) :: x2 :: x3 :: x4 :: x5 :: (UInt256.land x6 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: R)

/-- Final memory for bytecode block summary `midnight_block_5311`. -/
def midnight_block_5311_memory {mem : ByteArray} {x6 : UInt256} : ByteArray :=
  ((UInt256.shiftRight x6 (UInt256.ofNat 128)).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5311. -/
theorem midnight_block_5311 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5311) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) (midnight_block_5311_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (midnight_block_5311_memory (mem := mem) (x6 := x6)) (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 704) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 704) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r4 := r3.dup9 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.dup9 (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.swap8 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.swap3 (by native_decide) (by evm_ov)
  have r19 := r18.dup4 (by native_decide) (by evm_ov)
  have r20 := r19.swap3 (by native_decide) (by evm_ov)
  have r21 := r20.swap2 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5340)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5311_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5311) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) (midnight_block_5311_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (midnight_block_5311_memory (mem := mem) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5311 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5340. -/
theorem midnight_block_5340_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land (memLoad (UInt256.ofNat 704) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7846) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7846) R mem (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7846) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7846)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5340_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land (memLoad (UInt256.ofNat 704) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7846) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7846) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5340_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5340. -/
theorem midnight_block_5340_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land (memLoad (UInt256.ofNat 704) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5358) R mem (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7846) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5358)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5340_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land (memLoad (UInt256.ofNat 704) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5340) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5358) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5340_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5358`. -/
def midnight_block_5358_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 128) :: (UInt256.ofNat 5442) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `midnight_block_5358`. -/
def midnight_block_5358_memory {mem : ByteArray} {x8 : UInt256} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932).toByteArray.write 0 ((UInt256.land x8 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 768) mem).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5358. -/
theorem midnight_block_5358 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5358) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_5358_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_5358_memory (mem := mem) (x8 := x8)) (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((109) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.dup11 (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.pushConst (UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 5442) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r33 := r32.dup3 (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r35 := r34.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r35 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5358_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5358) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_5358_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_5358_memory (mem := mem) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5358 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5442_taken`. -/
def midnight_block_5442_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5442. -/
theorem midnight_block_5442_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7808) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5442) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7808) (midnight_block_5442_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (memLoad x0 mem)) rdata σ (k + 12) (C + ((35) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genKeccak256 r6 (by native_decide) (by evm_ov)
  have r8 := r7.tload (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 7808) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7808)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5442_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7808) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5442) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7808) (midnight_block_5442_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5442_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5442_fallthrough`. -/
def midnight_block_5442_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5442. -/
theorem midnight_block_5442_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5442) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (midnight_block_5442_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (memLoad x0 mem)) rdata σ (k + 12) (C + ((35) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genKeccak256 r6 (by native_decide) (by evm_ov)
  have r8 := r7.tload (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 7808) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5457)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5442_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (keccakWord (x0 + (UInt256.ofNat 32)) (memLoad x0 mem) mem) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5442) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (midnight_block_5442_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5442_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5457_taken`. -/
def midnight_block_5457_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5457. -/
theorem midnight_block_5457_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7787) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7787) (midnight_block_5457_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7787) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7787)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5457_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7787) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7787) (midnight_block_5457_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5457_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5457_fallthrough`. -/
def midnight_block_5457_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5457. -/
theorem midnight_block_5457_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (midnight_block_5457_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7787) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5463)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5457_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5457) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (midnight_block_5457_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5457_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5463. -/
theorem midnight_block_5463_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : x9 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7431) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7431) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.dup10 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7431) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7431)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5463_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : x9 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7431) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7431) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5463_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5463. -/
theorem midnight_block_5463_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : x9 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.dup10 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7431) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5468)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5463_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : x9 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5463) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5463_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5468_taken`. -/
def midnight_block_5468_taken_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5468. -/
theorem midnight_block_5468_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7420) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7420) (midnight_block_5468_taken_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7420) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7420)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5468_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7420) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7420) (midnight_block_5468_taken_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5468_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5468_fallthrough`. -/
def midnight_block_5468_fallthrough_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5468. -/
theorem midnight_block_5468_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (midnight_block_5468_fallthrough_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7420) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5475)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5468_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5468) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (midnight_block_5468_fallthrough_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5468_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5475_taken`. -/
def midnight_block_5475_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5475. -/
theorem midnight_block_5475_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6477) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6477) (midnight_block_5475_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6477) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6477)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5475_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6477) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6477) (midnight_block_5475_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5475_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_5475_fallthrough`. -/
def midnight_block_5475_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5475. -/
theorem midnight_block_5475_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5480) (midnight_block_5475_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6477) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5480)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_5475_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5475) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5480) (midnight_block_5475_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_5475_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
