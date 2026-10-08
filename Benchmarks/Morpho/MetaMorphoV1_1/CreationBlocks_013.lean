import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2943_taken`. -/
def metaMorphoV1_1Creation_block_2943_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x1 :: x2 :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2943. -/
theorem metaMorphoV1_1Creation_block_2943_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x1 (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3005) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3005) (metaMorphoV1_1Creation_block_2943_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 3005) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 3005) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3005)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2943_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x1 (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3005) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3005) (metaMorphoV1_1Creation_block_2943_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_2943_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2943_fallthrough`. -/
def metaMorphoV1_1Creation_block_2943_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x1 :: x2 :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2943. -/
theorem metaMorphoV1_1Creation_block_2943_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x1 (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (metaMorphoV1_1Creation_block_2943_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 3005) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2959)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2943_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.gt x1 (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (metaMorphoV1_1Creation_block_2943_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_2943_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2959_taken`. -/
def metaMorphoV1_1Creation_block_2959_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: (⟨0⟩ : UInt256) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2959. -/
theorem metaMorphoV1_1Creation_block_2959_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2994) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2994) (metaMorphoV1_1Creation_block_2959_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2994) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2994) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2994)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2959_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2994) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2994) (metaMorphoV1_1Creation_block_2959_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_2959_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2959_fallthrough`. -/
def metaMorphoV1_1Creation_block_2959_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: (⟨0⟩ : UInt256) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2959. -/
theorem metaMorphoV1_1Creation_block_2959_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (metaMorphoV1_1Creation_block_2959_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2994) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2969)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2959_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (metaMorphoV1_1Creation_block_2959_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_2959_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2969`. -/
def metaMorphoV1_1Creation_block_2969_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 255) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2969. -/
theorem metaMorphoV1_1Creation_block_2969 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x4 (metaMorphoV1_1Creation_block_2969_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3)))) x2) (UInt256.shiftLeft x3 (UInt256.ofNat 1)))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
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
  have r17 := r16.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sstore r17 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x4 hvalid) (by evm_ov)
  exact ⟨_, _, r21⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2969_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x4 (metaMorphoV1_1Creation_block_2969_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.shiftLeft x3 (UInt256.ofNat 3)))) x2) (UInt256.shiftLeft x3 (UInt256.ofNat 1)))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_2969 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_2994`. -/
def metaMorphoV1_1Creation_block_2994_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (memLoad (x0 + x1) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2994. -/
theorem metaMorphoV1_1Creation_block_2994 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2969) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2994) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (metaMorphoV1_1Creation_block_2994_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((28) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2969) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2969) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2969)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_2994_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2969) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2994) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2969) (metaMorphoV1_1Creation_block_2994_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_2994 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3005`. -/
def metaMorphoV1_1Creation_block_3005_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x3 :: (keccakWord (⟨0⟩ : UInt256) x3 ((UInt256.ofNat 5).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)) :: x1 :: x2 :: (UInt256.land x1 (UInt256.lnot (UInt256.ofNat 31))) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_3005`. -/
def metaMorphoV1_1Creation_block_3005_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 5).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3005. -/
theorem metaMorphoV1_1Creation_block_3005 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3005) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (metaMorphoV1_1Creation_block_3005_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_3005_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x3) rdata σ (k + 14) (C + ((34) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x3) + (30 + 6 * ((x3.toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3021)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3005_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3005) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (metaMorphoV1_1Creation_block_3005_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_3005_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3005 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem metaMorphoV1_1Creation_block_3021_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x0 x6) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3078) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3078) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3078) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 3078) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3078)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3021_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x0 x6) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3078) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3078) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3021_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem metaMorphoV1_1Creation_block_3021_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x0 x6) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3078) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3029)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3021_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x0 x6) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3021_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3029_taken`. -/
def metaMorphoV1_1Creation_block_3029_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: (UInt256.ofNat 1) :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3029. -/
theorem metaMorphoV1_1Creation_block_3029_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3054) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3054) (metaMorphoV1_1Creation_block_3029_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3054) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 3054) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3054)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3029_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3054) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3054) (metaMorphoV1_1Creation_block_3029_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3029_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3029_fallthrough`. -/
def metaMorphoV1_1Creation_block_3029_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: (UInt256.ofNat 1) :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3029. -/
theorem metaMorphoV1_1Creation_block_3029_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (metaMorphoV1_1Creation_block_3029_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3054) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3040)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3029_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x6 x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3029) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (metaMorphoV1_1Creation_block_3029_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3029_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3040`. -/
def metaMorphoV1_1Creation_block_3040_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 255) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3040. -/
theorem metaMorphoV1_1Creation_block_3040 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x5 (metaMorphoV1_1Creation_block_3040_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) ((UInt256.shiftLeft x3 x4) + x4)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sstore r8 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x5 hvalid) (by evm_ov)
  exact ⟨_, _, r12⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3040_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x5 (metaMorphoV1_1Creation_block_3040_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) ((UInt256.shiftLeft x3 x4) + x4)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_3040 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3054`. -/
def metaMorphoV1_1Creation_block_3054_stack {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3054. -/
theorem metaMorphoV1_1Creation_block_3054 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3040) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3054) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (metaMorphoV1_1Creation_block_3054_stack (x3 := x3) (R := R)) mem (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.land (UInt256.shiftLeft x3 (UInt256.ofNat 3)) (UInt256.ofNat 248)))) (memLoad (x0 + x1) mem))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 248) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sstore r14 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 3040) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 3040) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3040)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3054_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3040) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3054) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3040) (metaMorphoV1_1Creation_block_3054_stack (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.land (UInt256.shiftLeft x3 (UInt256.ofNat 3)) (UInt256.ofNat 248)))) (memLoad (x0 + x1) mem))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_3054 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3078`. -/
def metaMorphoV1_1Creation_block_3078_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 32)) :: x1 :: (x2 + (UInt256.ofNat 32)) :: (x3 + (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3078. -/
theorem metaMorphoV1_1Creation_block_3078 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3021) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3078) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (metaMorphoV1_1Creation_block_3078_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x1 + x2) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 (memLoad (x1 + x2) mem)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMload r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sstore r12 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 3021) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 3021) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3021)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3078_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3021) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3078) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3021) (metaMorphoV1_1Creation_block_3078_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 (memLoad (x1 + x2) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_3078 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3102`. -/
def metaMorphoV1_1Creation_block_3102_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.shiftRight (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 5)) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) ((UInt256.ofNat 5).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32))) :: ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) ((UInt256.ofNat 5).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)) + (UInt256.shiftRight (x0 + (UInt256.ofNat 31)) (UInt256.ofNat 5))) :: x1 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_3102`. -/
def metaMorphoV1_1Creation_block_3102_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 5).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3102. -/
theorem metaMorphoV1_1Creation_block_3102 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3102) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (metaMorphoV1_1Creation_block_3102_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_3102_memory (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) rdata σ (k + 21) (C + ((56) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (30 + 6 * (((UInt256.ofNat 32).toNat + 31) / 32)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genKeccak256 r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3129)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3102_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3102) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (metaMorphoV1_1Creation_block_3102_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_3102_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3102 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3129. -/
theorem metaMorphoV1_1Creation_block_3129_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3142) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3142) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3142) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 3142) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3142)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3129_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3142) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3142) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3129_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3129. -/
theorem metaMorphoV1_1Creation_block_3129_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3137) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3142) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3137)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3129_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3137) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3129_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3137`. -/
def metaMorphoV1_1Creation_block_3137_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3137. -/
theorem metaMorphoV1_1Creation_block_3137 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2943) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3137) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (metaMorphoV1_1Creation_block_3137_stack (R := R)) mem aw rdata σ (k + 3) (C + ((13))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2943) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2943) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2943)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3137_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2943) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3137) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2943) (metaMorphoV1_1Creation_block_3137_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3137 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3142`. -/
def metaMorphoV1_1Creation_block_3142_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3142. -/
theorem metaMorphoV1_1Creation_block_3142 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3129) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3142) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (metaMorphoV1_1Creation_block_3142_stack (x0 := x0) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x0 (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3129) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 3129) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3129)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3142_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 3129) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3142) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3129) (metaMorphoV1_1Creation_block_3142_stack (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x0 (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_3142 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_3153`. -/
def metaMorphoV1_1Creation_block_3153_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.land (UInt256.ofNat 127) x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3153. -/
theorem metaMorphoV1_1Creation_block_3153 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2925) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3153) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2925) (metaMorphoV1_1Creation_block_3153_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 127) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2925) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2925) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2925)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_3153_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2925) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 3153) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2925) (metaMorphoV1_1Creation_block_3153_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_3153 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
