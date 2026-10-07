import Reasoning.Reach
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 437. -/
theorem safeRuntime_block_437_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 223883027) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 437) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 223883027) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 633) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 449)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_437_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 223883027) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 437) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_437_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 449. -/
theorem safeRuntime_block_449_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 318466272) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 666) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 318466272) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 666) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 666)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_449_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 318466272) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 666) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_449_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 449. -/
theorem safeRuntime_block_449_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 318466272) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 318466272) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 666) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 460)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_449_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 318466272) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_449_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 460. -/
theorem safeRuntime_block_460_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 533383155) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 697) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 697) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 533383155) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 697) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 697)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_460_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 533383155) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 697) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 697) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_460_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 460. -/
theorem safeRuntime_block_460_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 533383155) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 471) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 533383155) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 697) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 471)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_460_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 533383155) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 460) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 471) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_460_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 471. -/
theorem safeRuntime_block_471 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 471) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 535) (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_471_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 471) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_471 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 475. -/
theorem safeRuntime_block_475_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.ofNat ee.calldata.size) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 475) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 535) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_475_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.ofNat ee.calldata.size) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 475) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_475_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 475. -/
theorem safeRuntime_block_475_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.ofNat ee.calldata.size) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 475) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 481) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 535) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 481)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_475_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.ofNat ee.calldata.size) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 475) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 481) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_475_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 481. -/
theorem safeRuntime_block_481 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 481) R mem aw rdata σ k C)
    : RDret Benchmarks.Safe.safeBytecode g s0 σ ByteArray.empty := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.callvalue (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.caller (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 27613899205238800472750487981127851187820584748339481801398827578897088740413) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.swap2 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := RD.genLog2 r17 (by native_decide) hperm (by evm_ov)
  exact r18.stop (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_535_taken`. -/
def safeRuntime_block_535_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 535. -/
theorem safeRuntime_block_535_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 546) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (safeRuntime_block_535_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 546) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 546)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_535_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 546) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (safeRuntime_block_535_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_535_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_535_fallthrough`. -/
def safeRuntime_block_535_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 535. -/
theorem safeRuntime_block_535_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 543) (safeRuntime_block_535_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 546) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 543)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_535_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 535) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 543) (safeRuntime_block_535_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_535_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 543. -/
theorem safeRuntime_block_543 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 543) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_546_taken`. -/
def safeRuntime_block_546_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 546. -/
theorem safeRuntime_block_546_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 588) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 588) (safeRuntime_block_546_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 588) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 588)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_546_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 588) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 588) (safeRuntime_block_546_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_546_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_546_fallthrough`. -/
def safeRuntime_block_546_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 546. -/
theorem safeRuntime_block_546_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 587) (safeRuntime_block_546_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 588) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 587)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_546_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 49122629484629529244014240937346711770925847994644146912111677022347558721749) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 587) (safeRuntime_block_546_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_546_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 587. -/
theorem safeRuntime_block_587 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 587) R mem aw rdata σ k C)
    : RDret Benchmarks.Safe.safeBytecode g s0 σ ByteArray.empty := by
  let r0 := h
  exact r0.stop (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_588`. -/
def safeRuntime_block_588_stack {ee : ExecutionEnv} {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((53) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) + (3 + 3 * (((UInt256.ofNat ee.calldata.size).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat ee.calldata.size)) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x0 :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 20)) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_588`. -/
def safeRuntime_block_588_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat ee.source.val) (UInt256.ofNat 96)).toByteArray.write 0 (ee.calldata.write (⟨0⟩ : UInt256).toNat mem (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat ee.calldata.size).toNat) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat ee.calldata.size)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 588. -/
theorem safeRuntime_block_588 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 588) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 614) (safeRuntime_block_588_stack (ee := ee) (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (R := R)) (safeRuntime_block_588_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat ee.calldata.size)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((55) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) + (3 + 3 * (((UInt256.ofNat ee.calldata.size).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat ee.calldata.size)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := RD.genCalldatacopy r6 (by native_decide) (by evm_ov)
  have r8 := r7.caller (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.calldatasize (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  have r18 := r17.calldatasize (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := r19.dup4 (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := r21.dup7 (by native_decide) (by evm_ov)
  have r23 := RD.genGas (RD.normalizeCounters (k' := k + 22) (C' := C + ((53) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) + (3 + 3 * (((UInt256.ofNat ee.calldata.size).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat ee.calldata.size)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat ee.calldata.size)) (⟨32⟩ : UInt256)))) r22 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 614)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_588_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 588) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 614) (safeRuntime_block_588_stack (ee := ee) (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (R := R)) (safeRuntime_block_588_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_588 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 614: call (0xf1). No RD transition is asserted. Summaries resume at pc 615 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_615_taken`. -/
def safeRuntime_block_615_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_615_taken`. -/
def safeRuntime_block_615_taken_memory {mem : ByteArray} {rdata : ByteArray} {x1 : UInt256} : ByteArray :=
  (rdata.write (⟨0⟩ : UInt256).toNat mem x1.toNat (UInt256.ofNat rdata.size).toNat)

/-- Automatically generated RD summary for bytecode block at pc 615. -/
theorem safeRuntime_block_615_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 629) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 615) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 629) (safeRuntime_block_615_taken_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_615_taken_memory (mem := mem) (rdata := rdata) (x1 := x1)) (M aw x1 (UInt256.ofNat rdata.size)) rdata σ (k + 9) (C + ((28) + (memExpansionCost aw x1 (UInt256.ofNat rdata.size)) + (3 + 3 * (((UInt256.ofNat rdata.size).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.returndatasize (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := RD.genReturndatacopy r5 (by native_decide) hguard0 (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 629) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 629)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_615_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 629) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 615) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 629) (safeRuntime_block_615_taken_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_615_taken_memory (mem := mem) (rdata := rdata) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_615_taken hstack hguard0 hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_615_fallthrough`. -/
def safeRuntime_block_615_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_615_fallthrough`. -/
def safeRuntime_block_615_fallthrough_memory {mem : ByteArray} {rdata : ByteArray} {x1 : UInt256} : ByteArray :=
  (rdata.write (⟨0⟩ : UInt256).toNat mem x1.toNat (UInt256.ofNat rdata.size).toNat)

/-- Automatically generated RD summary for bytecode block at pc 615. -/
theorem safeRuntime_block_615_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 615) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 626) (safeRuntime_block_615_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_615_fallthrough_memory (mem := mem) (rdata := rdata) (x1 := x1)) (M aw x1 (UInt256.ofNat rdata.size)) rdata σ (k + 9) (C + ((28) + (memExpansionCost aw x1 (UInt256.ofNat rdata.size)) + (3 + 3 * (((UInt256.ofNat rdata.size).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.returndatasize (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := RD.genReturndatacopy r5 (by native_decide) hguard0 (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 629) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 626)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_615_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 615) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 626) (safeRuntime_block_615_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_615_fallthrough_memory (mem := mem) (rdata := rdata) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_615_fallthrough hstack hguard0 hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 626. -/
theorem safeRuntime_block_626 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 626) (x0 :: R) mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 629. -/
theorem safeRuntime_block_629 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 629) (x0 :: R) mem aw rdata σ k C)
    : RDret Benchmarks.Safe.safeBytecode g s0 σ (mem.readWithPadding x0.toNat (UInt256.ofNat rdata.size).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  exact RD.genRet r3 (by native_decide) (by evm_ov)

end safeRuntimeBlocks
