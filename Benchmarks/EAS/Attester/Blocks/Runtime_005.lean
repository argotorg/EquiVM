import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.Attester.Immutables
import Benchmarks.EAS.Attester.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterRuntimeBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

/-- Automatically generated RD summary for bytecode block at pc 899. -/
theorem attesterRuntime_block_899 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 899) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 877) rfl).drop 17 899 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_903`. -/
def attesterRuntime_block_903_stack {g : Sat256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((3)) + 2)).toUInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 903. -/
theorem attesterRuntime_block_903 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 906) (attesterRuntime_block_903_stack (g := g) (C := C) (R := R)) mem aw rdata σ (k + 3) (C + ((5))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 903) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) d2.head (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_903_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 906) (attesterRuntime_block_903_stack (g := g) (C := C) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_903 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 906: call (0xf1). No RD transition is asserted. Summaries resume at pc 907 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `attesterRuntime_block_907_taken`. -/
def attesterRuntime_block_907_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 907. -/
theorem attesterRuntime_block_907_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 923) (attesterRuntime_block_907_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 903) rfl).drop 4 907 rfl
  have r1 := r0.iszero d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.iszero d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 923) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiT d4.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 923) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_907_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 923) (attesterRuntime_block_907_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_907_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_907_fallthrough`. -/
def attesterRuntime_block_907_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 907. -/
theorem attesterRuntime_block_907_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 914) (attesterRuntime_block_907_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 903) rfl).drop 4 907 rfl
  have r1 := r0.iszero d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.iszero d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 923) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiNT d4.head hcond (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_907_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 914) (attesterRuntime_block_907_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_907_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 914. -/
theorem attesterRuntime_block_914 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 914) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 903) rfl).drop 9 914 rfl
  have r1 := r0.returndatasize d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genReturndatacopy r3 d3.head (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.returndatasize d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 0) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  exact RD.genRev r6 d6.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_923`. -/
def attesterRuntime_block_923_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 923. -/
theorem attesterRuntime_block_923 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x10 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 923) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x10 (attesterRuntime_block_923_stack (R := R)) mem aw rdata σ (k + 12) (C + ((29))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 923) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.pop d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.pop d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.pop d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.pop d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.jump d11.head hvalid (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_923_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x10 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 923) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x10 (attesterRuntime_block_923_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_923 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_935_taken`. -/
def attesterRuntime_block_935_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x2) :: x2 :: (UInt256.ofNat 96) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 935. -/
theorem attesterRuntime_block_935_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (attesterRuntime_block_935_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 935) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 96) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup1 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push2 (UInt256.ofNat 951) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jumpiT d7.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 951) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_935_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (attesterRuntime_block_935_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_935_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_935_fallthrough`. -/
def attesterRuntime_block_935_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x2) :: x2 :: (UInt256.ofNat 96) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 935. -/
theorem attesterRuntime_block_935_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 946) (attesterRuntime_block_935_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 935) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 96) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup1 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push2 (UInt256.ofNat 951) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jumpiNT d7.head hcond (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_935_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 946) (attesterRuntime_block_935_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_935_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_946`. -/
def attesterRuntime_block_946_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq x3 x1)) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 946. -/
theorem attesterRuntime_block_946 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (attesterRuntime_block_946_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 5) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 935) rfl).drop 8 946 rfl
  have r1 := r0.pop d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.eq d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_946_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 946) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (attesterRuntime_block_946_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_946 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_951_taken`. -/
def attesterRuntime_block_951_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 951. -/
theorem attesterRuntime_block_951_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (attesterRuntime_block_951_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 951) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.iszero d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push2 (UInt256.ofNat 1006) d2.head (by evm_ov)
  have d3 := d2.next 3 rfl
  have r4 := r3.jumpiT d3.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1006) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_951_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (attesterRuntime_block_951_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_951_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_951_fallthrough`. -/
def attesterRuntime_block_951_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 951. -/
theorem attesterRuntime_block_951_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 957) (attesterRuntime_block_951_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 951) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.iszero d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push2 (UInt256.ofNat 1006) d2.head (by evm_ov)
  have d3 := d2.next 3 rfl
  have r4 := r3.jumpiNT d3.head hcond (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_951_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 951) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 957) (attesterRuntime_block_951_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_951_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 957. -/
theorem attesterRuntime_block_957 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 957) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 951) rfl).drop 4 957 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pushConst (UInt256.ofNat 81858464147032847215077304844434438867404723943161524698889464662459408187392) (width := 32) (op := .PUSH32) (by decide) d2.head (by evm_ov)
  have d3 := d2.next (Nat.succ 32) rfl
  have r4 := r3.dup2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := RD.genMstore r4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 4) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 64) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := RD.genMload r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.sub d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap1 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  exact RD.genRev r13 d13.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_1006_taken`. -/
def attesterRuntime_block_1006_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1006. -/
theorem attesterRuntime_block_1006_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (attesterRuntime_block_1006_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1006) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 1033) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiT d8.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1033) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1006_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (attesterRuntime_block_1006_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1006_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1006_fallthrough`. -/
def attesterRuntime_block_1006_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1006. -/
theorem attesterRuntime_block_1006_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1026) (attesterRuntime_block_1006_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1006) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 1033) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiNT d8.head hcond (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1006_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1006) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1026) (attesterRuntime_block_1006_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1006_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1026`. -/
def attesterRuntime_block_1026_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1033) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1026. -/
theorem attesterRuntime_block_1026 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1026) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_1026_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1006) rfl).drop 9 1026 rfl
  have r1 := r0.push2 (UInt256.ofNat 1033) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2696) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2696) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1026_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1026) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_1026_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1026 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1033_taken`. -/
def attesterRuntime_block_1033_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1033_taken`. -/
def attesterRuntime_block_1033_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1033. -/
theorem attesterRuntime_block_1033_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1103) (attesterRuntime_block_1033_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_1033_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1033) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 32) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.mul d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push1 (UInt256.ofNat 32) d10.head (by evm_ov)
  have d11 := d10.next 2 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup3 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push1 (UInt256.ofNat 64) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := RD.genMstore r15 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup1 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.iszero d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push2 (UInt256.ofNat 1103) d18.head (by evm_ov)
  have d19 := d18.next 3 rfl
  have r20 := r19.jumpiT d19.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1103) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r20 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1033_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1103) (attesterRuntime_block_1033_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_1033_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1033_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1033_fallthrough`. -/
def attesterRuntime_block_1033_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1033_fallthrough`. -/
def attesterRuntime_block_1033_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1033. -/
theorem attesterRuntime_block_1033_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1059) (attesterRuntime_block_1033_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_1033_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1033) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 32) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.mul d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push1 (UInt256.ofNat 32) d10.head (by evm_ov)
  have d11 := d10.next 2 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup3 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push1 (UInt256.ofNat 64) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := RD.genMstore r15 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup1 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.iszero d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push2 (UInt256.ofNat 1103) d18.head (by evm_ov)
  have d19 := d18.next 3 rfl
  have r20 := r19.jumpiNT d19.head hcond (by evm_ov)
  exact RD.normalizeCounters r20 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1033_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1033) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1059) (attesterRuntime_block_1033_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_1033_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1033_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1059`. -/
def attesterRuntime_block_1059_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1059. -/
theorem attesterRuntime_block_1059 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1059) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (attesterRuntime_block_1059_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((9))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1033) rfl).drop 20 1059 rfl
  have r1 := r0.dup2 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.add d2.head (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1059_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1059) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (attesterRuntime_block_1059_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1059 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1063_taken`. -/
def attesterRuntime_block_1063_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1063_taken`. -/
def attesterRuntime_block_1063_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1063. -/
theorem attesterRuntime_block_1063_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (attesterRuntime_block_1063_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_1063_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1063) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.swap2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := RD.genMstore r9 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push1 (UInt256.ofNat 0) d10.head (by evm_ov)
  have d11 := d10.next 2 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 96) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.push1 (UInt256.ofNat 32) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := r15.dup3 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := RD.genMstore r17 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push1 (UInt256.ofNat 32) d20.head (by evm_ov)
  have d21 := d20.next 2 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.swap1 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.push1 (UInt256.ofNat 1) d23.head (by evm_ov)
  have d24 := d23.next 2 rfl
  have r25 := r24.swap1 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.sub d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.swap1 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.dup2 d27.head (by evm_ov)
  have d28 := d27.next 1 rfl
  have r29 := r28.push2 (UInt256.ofNat 1063) d28.head (by evm_ov)
  have d29 := d28.next 3 rfl
  have r30 := r29.jumpiT d29.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1063) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r30 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1063_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (attesterRuntime_block_1063_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_1063_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1063_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1063_fallthrough`. -/
def attesterRuntime_block_1063_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1063_fallthrough`. -/
def attesterRuntime_block_1063_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1063. -/
theorem attesterRuntime_block_1063_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1101) (attesterRuntime_block_1063_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_1063_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1063) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.swap2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := RD.genMstore r9 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push1 (UInt256.ofNat 0) d10.head (by evm_ov)
  have d11 := d10.next 2 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 96) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.push1 (UInt256.ofNat 32) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := r15.dup3 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := RD.genMstore r17 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push1 (UInt256.ofNat 32) d20.head (by evm_ov)
  have d21 := d20.next 2 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.swap1 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.push1 (UInt256.ofNat 1) d23.head (by evm_ov)
  have d24 := d23.next 2 rfl
  have r25 := r24.swap1 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.sub d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.swap1 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.dup2 d27.head (by evm_ov)
  have d28 := d27.next 1 rfl
  have r29 := r28.push2 (UInt256.ofNat 1063) d28.head (by evm_ov)
  have d29 := d28.next 3 rfl
  have r30 := r29.jumpiNT d29.head hcond (by evm_ov)
  exact RD.normalizeCounters r30 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1063_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1101) (attesterRuntime_block_1063_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_1063_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1063_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
