import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_392_fallthrough`. -/
def metaMorphoV1_1Creation_block_392_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x12 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 392. -/
theorem metaMorphoV1_1Creation_block_392_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x2 (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 392) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (metaMorphoV1_1Creation_block_392_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 2195) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 407)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_392_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x2 (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 392) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (metaMorphoV1_1Creation_block_392_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_392_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_407_taken`. -/
def metaMorphoV1_1Creation_block_407_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 407. -/
theorem metaMorphoV1_1Creation_block_407_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2184) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2184) (metaMorphoV1_1Creation_block_407_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2184) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2184) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2184)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_407_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2184) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2184) (metaMorphoV1_1Creation_block_407_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_407_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_407_fallthrough`. -/
def metaMorphoV1_1Creation_block_407_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 407. -/
theorem metaMorphoV1_1Creation_block_407_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 413) (metaMorphoV1_1Creation_block_407_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2184) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 413)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_407_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 413) (metaMorphoV1_1Creation_block_407_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_407_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_413`. -/
def metaMorphoV1_1Creation_block_413_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 413. -/
theorem metaMorphoV1_1Creation_block_413 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 413) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 434) (metaMorphoV1_1Creation_block_413_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3)))) x2) (UInt256.shiftLeft x3 (UInt256.ofNat 1)))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sstore r17 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 434)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_413_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 413) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 434) (metaMorphoV1_1Creation_block_413_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3)))) x2) (UInt256.shiftLeft x3 (UInt256.ofNat 1)))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_413 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_434`. -/
def metaMorphoV1_1Creation_block_434_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x6 :: (UInt256.ofNat 443) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 434. -/
theorem metaMorphoV1_1Creation_block_434 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3545) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 434) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3545) (metaMorphoV1_1Creation_block_434_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 443) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3545) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 3545) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3545)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_434_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3545) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 434) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3545) (metaMorphoV1_1Creation_block_434_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_434 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_443_taken`. -/
def metaMorphoV1_1Creation_block_443_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 443. -/
theorem metaMorphoV1_1Creation_block_443_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2176) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2176) (metaMorphoV1_1Creation_block_443_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2176) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2176) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2176)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_443_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2176) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2176) (metaMorphoV1_1Creation_block_443_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_443_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_443_fallthrough`. -/
def metaMorphoV1_1Creation_block_443_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 443. -/
theorem metaMorphoV1_1Creation_block_443_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 450) (metaMorphoV1_1Creation_block_443_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2176) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 450)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_443_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 450) (metaMorphoV1_1Creation_block_443_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_443_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_450`. -/
def metaMorphoV1_1Creation_block_450_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 466) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_450`. -/
def metaMorphoV1_1Creation_block_450_memory {mem : ByteArray} {x0 : UInt256} {x7 : UInt256} : ByteArray :=
  (x7.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 450. -/
theorem metaMorphoV1_1Creation_block_450 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2802) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2802) (metaMorphoV1_1Creation_block_450_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (metaMorphoV1_1Creation_block_450_memory (mem := mem) (x0 := x0) (x7 := x7)) (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((33) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 466) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2802) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2802) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2802)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_450_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2802) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2802) (metaMorphoV1_1Creation_block_450_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (metaMorphoV1_1Creation_block_450_memory (mem := mem) (x0 := x0) (x7 := x7)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_450 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_466`. -/
def metaMorphoV1_1Creation_block_466_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.ofNat 479) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_466`. -/
def metaMorphoV1_1Creation_block_466_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 466. -/
theorem metaMorphoV1_1Creation_block_466 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3174) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3174) (metaMorphoV1_1Creation_block_466_stack (x1 := x1) (x2 := x2) (R := R)) (metaMorphoV1_1Creation_block_466_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 352) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 479) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3174) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 3174) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3174)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_466_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3174) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3174) (metaMorphoV1_1Creation_block_466_stack (x1 := x1) (x2 := x2) (R := R)) (metaMorphoV1_1Creation_block_466_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_466 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_479`. -/
def metaMorphoV1_1Creation_block_479_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) :: (UInt256.ofNat 192) :: (UInt256.ofNat 588) :: (memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) :: ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_479`. -/
def metaMorphoV1_1Creation_block_479_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x9 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 63076024560530113402979550242307453568063438748328787417531900361828837441551).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9).toNat 32) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10).toNat 32) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 128)).toNat 32) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 160)).toNat 32) (memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 479. -/
theorem metaMorphoV1_1Creation_block_479 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2608) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2608) (metaMorphoV1_1Creation_block_479_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (metaMorphoV1_1Creation_block_479_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x9 := x9) (x10 := x10)) (M (M (M (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 61) (C + ((177) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) + (30 + 6 * (((memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toNat + 31) / 32)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) + (30 + 6 * (((memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32))) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32))) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x9) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + x10) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (memLoad x10 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((keccakWord (x2 + x9) (memLoad x2 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)) ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32)).toByteArray.write 0 ((keccakWord (x1 + x9) (memLoad x1 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 224).toNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 288) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := RD.genMstore r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMload r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 320) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genMstore r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.chainid (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMstore r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := RD.genMload r26 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.pushConst (UInt256.ofNat 63076024560530113402979550242307453568063438748328787417531900361828837441551) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := RD.genMstore r34 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := RD.genMstore r38 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := RD.genMstore r42 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.chainid (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := RD.genMstore r47 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.address (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := RD.genMstore r52 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := RD.genMstore r55 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.push2 (UInt256.ofNat 588) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 2608) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2608) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2608)) r61 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_479_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2608) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2608) (metaMorphoV1_1Creation_block_479_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (metaMorphoV1_1Creation_block_479_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x9 := x9) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_479 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_588_taken`. -/
def metaMorphoV1_1Creation_block_588_taken_stack {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_588_taken`. -/
def metaMorphoV1_1Creation_block_588_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 588. -/
theorem metaMorphoV1_1Creation_block_588_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2157) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2157) (metaMorphoV1_1Creation_block_588_taken_stack (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_588_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((61) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.address (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 2157) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2157) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2157)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_588_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2157) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2157) (metaMorphoV1_1Creation_block_588_taken_stack (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_588_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_588_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_588_fallthrough`. -/
def metaMorphoV1_1Creation_block_588_fallthrough_stack {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_588_fallthrough`. -/
def metaMorphoV1_1Creation_block_588_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 588. -/
theorem metaMorphoV1_1Creation_block_588_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (metaMorphoV1_1Creation_block_588_fallthrough_stack (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_588_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((61) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.address (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 2157) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 616)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_588_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (metaMorphoV1_1Creation_block_588_fallthrough_stack (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_588_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_588_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_616_taken`. -/
def metaMorphoV1_1Creation_block_616_taken_stack {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: (memLoad x7 mem) :: x2 :: x3 :: x4 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0) :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 616. -/
theorem metaMorphoV1_1Creation_block_616_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2142) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2142) (metaMorphoV1_1Creation_block_616_taken_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x7 (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))) (UInt256.ofNat 8) (UInt256.lor x1 (UInt256.land ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sstore r14 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 8) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sstore r24 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := RD.genMload r26 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.pushConst (UInt256.ofNat 63267312222310607310220992301550539520881909915348243260808268974908359596000) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := RD.genLog3 r38 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 2142) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2142) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2142)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_616_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2142) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2142) (metaMorphoV1_1Creation_block_616_taken_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))) (UInt256.ofNat 8) (UInt256.lor x1 (UInt256.land ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_616_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_616_fallthrough`. -/
def metaMorphoV1_1Creation_block_616_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: (memLoad x7 mem) :: x2 :: x3 :: x4 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0) :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 616. -/
theorem metaMorphoV1_1Creation_block_616_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (metaMorphoV1_1Creation_block_616_fallthrough_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x7 (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))) (UInt256.ofNat 8) (UInt256.lor x1 (UInt256.land ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sstore r14 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 8) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sstore r24 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := RD.genMload r26 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.pushConst (UInt256.ofNat 63267312222310607310220992301550539520881909915348243260808268974908359596000) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := RD.genLog3 r38 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 2142) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 711)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_616_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 616) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (metaMorphoV1_1Creation_block_616_fallthrough_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))) (UInt256.ofNat 8) (UInt256.lor x1 (UInt256.land ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 9) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_616_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 711. -/
theorem metaMorphoV1_1Creation_block_711_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2091) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2091) (x0 :: R) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2091) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2091) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2091)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_711_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2091) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2091) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_711_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 711. -/
theorem metaMorphoV1_1Creation_block_711_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: R) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2091) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 716)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_711_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 711) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_711_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_716_taken`. -/
def metaMorphoV1_1Creation_block_716_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_716_taken`. -/
def metaMorphoV1_1Creation_block_716_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 716. -/
theorem metaMorphoV1_1Creation_block_716_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 1854) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1854) (metaMorphoV1_1Creation_block_716_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (metaMorphoV1_1Creation_block_716_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x1 (⟨32⟩ : UInt256)) x1 x6) x2 (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 14) x0) (UInt256.ofNat 17) (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 95237664163728723080787522074639078529886382662028531352509654670117794627445) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genLog2 r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r12 := r11.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 17) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMload r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1854) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1854) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1854)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_716_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 1854) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1854) (metaMorphoV1_1Creation_block_716_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (metaMorphoV1_1Creation_block_716_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 14) x0) (UInt256.ofNat 17) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_716_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_716_fallthrough`. -/
def metaMorphoV1_1Creation_block_716_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_716_fallthrough`. -/
def metaMorphoV1_1Creation_block_716_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 716. -/
theorem metaMorphoV1_1Creation_block_716_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) (metaMorphoV1_1Creation_block_716_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (metaMorphoV1_1Creation_block_716_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x1 (⟨32⟩ : UInt256)) x1 x6) x2 (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 14) x0) (UInt256.ofNat 17) (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 95237664163728723080787522074639078529886382662028531352509654670117794627445) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genLog2 r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r12 := r11.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 17) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMload r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1854) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 780)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_716_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (memLoad x2 (x0.toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 716) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) (metaMorphoV1_1Creation_block_716_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (metaMorphoV1_1Creation_block_716_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 14) x0) (UInt256.ofNat 17) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_716_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_780_taken`. -/
def metaMorphoV1_1Creation_block_780_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1)) :: (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 780. -/
theorem metaMorphoV1_1Creation_block_780_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2081) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2081) (metaMorphoV1_1Creation_block_780_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 2081) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2081) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2081)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_780_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2081) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2081) (metaMorphoV1_1Creation_block_780_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_780_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_780_fallthrough`. -/
def metaMorphoV1_1Creation_block_780_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1)) :: (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 780. -/
theorem metaMorphoV1_1Creation_block_780_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 796) (metaMorphoV1_1Creation_block_780_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 2081) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 796)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_780_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 780) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 796) (metaMorphoV1_1Creation_block_780_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_780_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
