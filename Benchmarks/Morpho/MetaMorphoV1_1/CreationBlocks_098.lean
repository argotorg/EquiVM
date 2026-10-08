import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21925_fallthrough`. -/
def metaMorphoV1_1Creation_block_21925_fallthrough_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 18102) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21925. -/
theorem metaMorphoV1_1Creation_block_21925_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21925) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21935) (metaMorphoV1_1Creation_block_21925_fallthrough_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 18102) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 18249) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21935)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21925_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21925) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21935) (metaMorphoV1_1Creation_block_21925_fallthrough_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21925_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21935`. -/
def metaMorphoV1_1Creation_block_21935_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x1 :: (UInt256.ofNat ee.codeOwner.val) :: (UInt256.ofNat 18077) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21935. -/
theorem metaMorphoV1_1Creation_block_21935 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 14036) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21935) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (metaMorphoV1_1Creation_block_21935_stack (ee := ee) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ (k + 9) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18077) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.address (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 14036) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 14036) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14036)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21935_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 14036) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21935) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (metaMorphoV1_1Creation_block_21935_stack (ee := ee) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21935 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21948`. -/
def metaMorphoV1_1Creation_block_21948_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: (UInt256.land (memLoad (x1 + (UInt256.ofNat 32)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21948. -/
theorem metaMorphoV1_1Creation_block_21948 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 17613) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21948) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17613) (metaMorphoV1_1Creation_block_21948_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((60) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMload r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 17613) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 17613) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17613)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21948_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 17613) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21948) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17613) (metaMorphoV1_1Creation_block_21948_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21948 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21973_taken`. -/
def metaMorphoV1_1Creation_block_21973_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21973. -/
theorem metaMorphoV1_1Creation_block_21973_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18144) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21973) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18144) (metaMorphoV1_1Creation_block_21973_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 22) (C + ((75))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 18144) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 18144) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18144)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21973_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18144) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21973) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18144) (metaMorphoV1_1Creation_block_21973_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21973_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21973_fallthrough`. -/
def metaMorphoV1_1Creation_block_21973_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21973. -/
theorem metaMorphoV1_1Creation_block_21973_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21973) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (metaMorphoV1_1Creation_block_21973_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 22) (C + ((75))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 18144) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21997)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21973_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) (UInt256.mul (UInt256.xor (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0)) x5) (UInt256.lt x5 (UInt256.mul (UInt256.gt x1 x0) (UInt256.sub x1 x0))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21973) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (metaMorphoV1_1Creation_block_21973_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21973_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21997_taken`. -/
def metaMorphoV1_1Creation_block_21997_taken_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21997. -/
theorem metaMorphoV1_1Creation_block_21997_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12537) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12537) (metaMorphoV1_1Creation_block_21997_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12537) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12537) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12537)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21997_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12537) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12537) (metaMorphoV1_1Creation_block_21997_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21997_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_21997_fallthrough`. -/
def metaMorphoV1_1Creation_block_21997_fallthrough_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21997. -/
theorem metaMorphoV1_1Creation_block_21997_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22006) (metaMorphoV1_1Creation_block_21997_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12537) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22006)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_21997_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 21997) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22006) (metaMorphoV1_1Creation_block_21997_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_21997_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22006`. -/
def metaMorphoV1_1Creation_block_22006_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22006. -/
theorem metaMorphoV1_1Creation_block_22006 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22006) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22009) (metaMorphoV1_1Creation_block_22006_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((6))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22009)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22006_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22006) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22009) (metaMorphoV1_1Creation_block_22006_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22006 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22009`. -/
def metaMorphoV1_1Creation_block_22009_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22009. -/
theorem metaMorphoV1_1Creation_block_22009 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 17895) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22009) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17895) (metaMorphoV1_1Creation_block_22009_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 17895) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 17895) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17895)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22009_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 17895) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22009) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17895) (metaMorphoV1_1Creation_block_22009_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22009 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22015`. -/
def metaMorphoV1_1Creation_block_22015_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: x0 :: x1 :: (UInt256.ofNat ee.codeOwner.val) :: (UInt256.ofNat 18178) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 64) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_22015`. -/
def metaMorphoV1_1Creation_block_22015_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 2845486473) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 22015. -/
theorem metaMorphoV1_1Creation_block_22015 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12133) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22015) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (metaMorphoV1_1Creation_block_22015_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_22015_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18178) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push4 (UInt256.ofNat 2845486473) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMstore r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.address (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 12133) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12133) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12133)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22015_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12133) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22015) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (metaMorphoV1_1Creation_block_22015_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_22015_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22015 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22049`. -/
def metaMorphoV1_1Creation_block_22049_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((12)) + 2)).toUInt256) :: x7 :: (⟨0⟩ : UInt256) :: x2 :: (UInt256.sub x0 x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22049. -/
theorem metaMorphoV1_1Creation_block_22049 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22049) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22055) (metaMorphoV1_1Creation_block_22049_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 6) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genGas (RD.normalizeCounters (k' := k + 5) (C' := C + ((12))) r5 (by omega) (by omega)) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22055)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22049_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22049) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22055) (metaMorphoV1_1Creation_block_22049_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22049 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 22055: call (0xf1). No RD transition is asserted. Summaries resume at pc 22056 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22056_taken`. -/
def metaMorphoV1_1Creation_block_22056_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22056. -/
theorem metaMorphoV1_1Creation_block_22056_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18220) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22056) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18220) (metaMorphoV1_1Creation_block_22056_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18220) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 18220) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18220)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22056_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18220) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22056) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18220) (metaMorphoV1_1Creation_block_22056_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22056_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22056_fallthrough`. -/
def metaMorphoV1_1Creation_block_22056_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22056. -/
theorem metaMorphoV1_1Creation_block_22056_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22056) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (metaMorphoV1_1Creation_block_22056_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18220) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22062)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22056_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22056) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (metaMorphoV1_1Creation_block_22056_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22056_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22062_taken`. -/
def metaMorphoV1_1Creation_block_22062_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 22062. -/
theorem metaMorphoV1_1Creation_block_22062_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18203) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18203) (metaMorphoV1_1Creation_block_22062_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18203) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 18203) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18203)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22062_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18203) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18203) (metaMorphoV1_1Creation_block_22062_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22062_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22062_fallthrough`. -/
def metaMorphoV1_1Creation_block_22062_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 22062. -/
theorem metaMorphoV1_1Creation_block_22062_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22068) (metaMorphoV1_1Creation_block_22062_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18203) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22068)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22062_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22062) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22068) (metaMorphoV1_1Creation_block_22062_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22062_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22068`. -/
def metaMorphoV1_1Creation_block_22068_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22068. -/
theorem metaMorphoV1_1Creation_block_22068 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18126) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22068) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18126) (metaMorphoV1_1Creation_block_22068_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18126) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18126) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18126)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22068_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18126) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22068) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18126) (metaMorphoV1_1Creation_block_22068_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22068 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22074`. -/
def metaMorphoV1_1Creation_block_22074_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: (UInt256.ofNat 18213) :: x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22074. -/
theorem metaMorphoV1_1Creation_block_22074 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22074) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12192) (metaMorphoV1_1Creation_block_22074_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12192) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12192)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22074_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22074) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12192) (metaMorphoV1_1Creation_block_22074_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22074 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22084`. -/
def metaMorphoV1_1Creation_block_22084_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 22084. -/
theorem metaMorphoV1_1Creation_block_22084 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18197) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1Creation_block_22084_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 18197) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18197) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18197)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22084_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 18197) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22084) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1Creation_block_22084_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22084 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22091_taken`. -/
def metaMorphoV1_1Creation_block_22091_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: x0 :: (UInt256.ofNat 18243) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22091. -/
theorem metaMorphoV1_1Creation_block_22091_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 6359) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22091) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 6359) (metaMorphoV1_1Creation_block_22091_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18243) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6359) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 6359) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6359)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22091_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 6359) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22091) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 6359) (metaMorphoV1_1Creation_block_22091_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22091_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_22091_fallthrough`. -/
def metaMorphoV1_1Creation_block_22091_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: x0 :: (UInt256.ofNat 18243) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22091. -/
theorem metaMorphoV1_1Creation_block_22091_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22091) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22105) (metaMorphoV1_1Creation_block_22091_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18243) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6359) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22105)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_22091_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22091) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22105) (metaMorphoV1_1Creation_block_22091_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_22091_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
