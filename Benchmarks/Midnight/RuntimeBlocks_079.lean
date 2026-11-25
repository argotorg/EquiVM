import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_20760`. -/
def midnight_block_20760_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20760. -/
theorem midnight_block_20760 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20760) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_20760_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20760_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20760) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_20760_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20760 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20764. -/
theorem midnight_block_20764_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat Ethereum.chainId) (memLoad x1 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21820) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20764) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21820) (x0 :: x1 :: R) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.chainid (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21820) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21820)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20764_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat Ethereum.chainId) (memLoad x1 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21820) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20764) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21820) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20764_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20764. -/
theorem midnight_block_20764_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat Ethereum.chainId) (memLoad x1 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20764) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: x1 :: R) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.chainid (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21820) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20773)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20764_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat Ethereum.chainId) (memLoad x1 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20764) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20764_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20773_taken`. -/
def midnight_block_20773_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20773. -/
theorem midnight_block_20773_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.codeOwner.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad x0 mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21805) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21805) (midnight_block_20773_taken_stack (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((39) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.address (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 21805) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21805)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20773_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.codeOwner.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad x0 mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21805) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21805) (midnight_block_20773_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20773_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20773_fallthrough`. -/
def midnight_block_20773_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20773. -/
theorem midnight_block_20773_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.codeOwner.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad x0 mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (midnight_block_20773_fallthrough_stack (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((39) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.address (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 21805) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20789)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20773_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.codeOwner.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad x0 mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20773) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (midnight_block_20773_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20773_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20789_taken`. -/
def midnight_block_20789_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x0 + (UInt256.ofNat 128)) mem) :: ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20789. -/
theorem midnight_block_20789_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat ee.header.timestamp) ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20789_taken_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem (M aw (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 3153600000) (by native_decide) (by evm_ov)
  have r6 := r5.timestamp (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.timestamp (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20789_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat ee.header.timestamp) ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20789_taken_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20789_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20789_fallthrough`. -/
def midnight_block_20789_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x0 + (UInt256.ofNat 128)) mem) :: ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20789. -/
theorem midnight_block_20789_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat ee.header.timestamp) ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (midnight_block_20789_fallthrough_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem (M aw (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 3153600000) (by native_decide) (by evm_ov)
  have r6 := r5.timestamp (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.timestamp (by native_decide) (by evm_ov)
  have r11 := r10.gt (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20809)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20789_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat ee.header.timestamp) ((UInt256.ofNat ee.header.timestamp) + (UInt256.ofNat 3153600000))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20789) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (midnight_block_20789_fallthrough_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20789_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20809_taken`. -/
def midnight_block_20809_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20809. -/
theorem midnight_block_20809_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21790) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21790) (midnight_block_20809_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.gt (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 21790) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21790)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20809_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21790) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21790) (midnight_block_20809_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20809_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20809_fallthrough`. -/
def midnight_block_20809_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20809. -/
theorem midnight_block_20809_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (midnight_block_20809_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.gt (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 21790) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20814)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20809_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.gt x0 x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20809) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (midnight_block_20809_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20809_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20814_taken`. -/
def midnight_block_20814_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x0 + (UInt256.ofNat 96)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20814. -/
theorem midnight_block_20814_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (memLoad (x0 + (UInt256.ofNat 96)) mem) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21775) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21775) (midnight_block_20814_taken_stack (x0 := x0) (R := R)) mem (M (M aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((37) + (memExpansionCost aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 21775) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21775)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20814_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (memLoad (x0 + (UInt256.ofNat 96)) mem) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21775) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21775) (midnight_block_20814_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20814_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20814_fallthrough`. -/
def midnight_block_20814_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x0 + (UInt256.ofNat 96)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20814. -/
theorem midnight_block_20814_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (memLoad (x0 + (UInt256.ofNat 96)) mem) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (midnight_block_20814_fallthrough_stack (x0 := x0) (R := R)) mem (M (M aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((37) + (memExpansionCost aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 21775) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20827)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20814_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (memLoad (x0 + (UInt256.ofNat 96)) mem) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20814) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (midnight_block_20814_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20814_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20827. -/
theorem midnight_block_20827_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (memLoad x1 mem) mem) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21760) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21760) (x0 :: x1 :: R) mem (M (M aw x1 (⟨32⟩ : UInt256)) (memLoad x1 mem) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (memLoad x1 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21760) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20827_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (memLoad x1 mem) mem) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21760) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21760) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20827_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20827. -/
theorem midnight_block_20827_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (memLoad x1 mem) mem) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20837) (x0 :: x1 :: R) mem (M (M aw x1 (⟨32⟩ : UInt256)) (memLoad x1 mem) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (memLoad x1 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 21760) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20837)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20827_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (memLoad (memLoad x1 mem) mem) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20837) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20837`. -/
def midnight_block_20837_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x3 :: x0 :: x1 :: x2 :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20837. -/
theorem midnight_block_20837 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20837) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (midnight_block_20837_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 3) (C + ((8))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20840)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20837_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20837) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (midnight_block_20837_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20837 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20840_taken`. -/
def midnight_block_20840_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x3 mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20840. -/
theorem midnight_block_20840_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x5 (memLoad (memLoad x3 mem) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21130) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21130) (midnight_block_20840_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup8 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 21130) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21130)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20840_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x5 (memLoad (memLoad x3 mem) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21130) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21130) (midnight_block_20840_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20840_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20840_fallthrough`. -/
def midnight_block_20840_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x3 mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20840. -/
theorem midnight_block_20840_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x5 (memLoad (memLoad x3 mem) mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20852) (midnight_block_20840_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup8 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 21130) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20852)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20840_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x5 (memLoad (memLoad x3 mem) mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20840) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20852) (midnight_block_20840_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20840_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20852`. -/
def midnight_block_20852_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x6 :: (UInt256.ofNat 20870) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20852. -/
theorem midnight_block_20852 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20852) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20852_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20870) (by native_decide) (by evm_ov)
  have r7 := r6.dup9 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.swap4 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 19460) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19460)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20852_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20852) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20852_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20852 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20870_taken`. -/
def midnight_block_20870_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad (memLoad x0 mem) mem) x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20870. -/
theorem midnight_block_20870_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (memLoad (memLoad x0 mem) mem) x1) (UInt256.land x3 x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21115) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20870) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21115) (midnight_block_20870_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) (memLoad x0 mem) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (memLoad x0 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 21115) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21115)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20870_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (memLoad (memLoad x0 mem) mem) x1) (UInt256.land x3 x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21115) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20870) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21115) (midnight_block_20870_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20870_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20870_fallthrough`. -/
def midnight_block_20870_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad (memLoad x0 mem) mem) x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20870. -/
theorem midnight_block_20870_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (memLoad (memLoad x0 mem) mem) x1) (UInt256.land x3 x2))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20870) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20883) (midnight_block_20870_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) (memLoad x0 mem) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (memLoad x0 mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 21115) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20883)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20870_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (memLoad (memLoad x0 mem) mem) x1) (UInt256.land x3 x2))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20870) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20883) (midnight_block_20870_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20870_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20883`. -/
def midnight_block_20883_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x3 mem) :: x5 :: (UInt256.ofNat 20895) :: (UInt256.ofNat 32) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20883. -/
theorem midnight_block_20883 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20883) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20883_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 20895) (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.dup7 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19460) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19460)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20883_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19460) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20883) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19460) (midnight_block_20883_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20883 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
