import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 14784. -/
theorem metaMorphoV1_1Creation_block_14784_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14784) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14795) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14795)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14784_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14784) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14795) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14784_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14795`. -/
def metaMorphoV1_1Creation_block_14795_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 10916) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 24) (⟨0⟩ : UInt256))) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14795. -/
theorem metaMorphoV1_1Creation_block_14795 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11801) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14795) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11801) (metaMorphoV1_1Creation_block_14795_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 10916) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11801) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11801) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11801)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14795_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11801) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14795) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11801) (metaMorphoV1_1Creation_block_14795_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_14795 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14810_taken`. -/
def metaMorphoV1_1Creation_block_14810_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.land x1 (UInt256.ofNat 1)) :: x0 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_14810_taken`. -/
def metaMorphoV1_1Creation_block_14810_taken_memory {mem : ByteArray} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x3.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14810. -/
theorem metaMorphoV1_1Creation_block_14810_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 4753) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14810) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 4753) (metaMorphoV1_1Creation_block_14810_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14810_taken_memory (mem := mem) (x0 := x0) (x3 := x3)) (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 4753) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 4753) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4753)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14810_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 4753) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14810) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 4753) (metaMorphoV1_1Creation_block_14810_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14810_taken_memory (mem := mem) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14810_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14810_fallthrough`. -/
def metaMorphoV1_1Creation_block_14810_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.land x1 (UInt256.ofNat 1)) :: x0 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_14810_fallthrough`. -/
def metaMorphoV1_1Creation_block_14810_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x3.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14810. -/
theorem metaMorphoV1_1Creation_block_14810_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14810) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (metaMorphoV1_1Creation_block_14810_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14810_fallthrough_memory (mem := mem) (x0 := x0) (x3 := x3)) (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 4753) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14826)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14810_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x1 (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14810) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (metaMorphoV1_1Creation_block_14810_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14810_fallthrough_memory (mem := mem) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14810_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14826_taken`. -/
def metaMorphoV1_1Creation_block_14826_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14826. -/
theorem metaMorphoV1_1Creation_block_14826_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10955) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10955) (metaMorphoV1_1Creation_block_14826_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 10955) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 10955) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10955)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14826_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10955) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10955) (metaMorphoV1_1Creation_block_14826_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14826_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14826_fallthrough`. -/
def metaMorphoV1_1Creation_block_14826_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14826. -/
theorem metaMorphoV1_1Creation_block_14826_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14834) (metaMorphoV1_1Creation_block_14826_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 10955) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14834)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14826_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14834) (metaMorphoV1_1Creation_block_14826_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14826_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14834`. -/
def metaMorphoV1_1Creation_block_14834_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.sub x1 x2) :: (UInt256.ofNat 2379) :: x2 :: (UInt256.ofNat 4335) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14834. -/
theorem metaMorphoV1_1Creation_block_14834 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14834) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11329) (metaMorphoV1_1Creation_block_14834_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 4335) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2379) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11329) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11329) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11329)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14834_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14834) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11329) (metaMorphoV1_1Creation_block_14834_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14834 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14849`. -/
def metaMorphoV1_1Creation_block_14849_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (⟨0⟩ : UInt256) :: x2 :: (UInt256.ofNat 80167465652159884487584418398737133515478493586045375474096367959472086682926) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_14849`. -/
def metaMorphoV1_1Creation_block_14849_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 24).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14849. -/
theorem metaMorphoV1_1Creation_block_14849 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14849) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (metaMorphoV1_1Creation_block_14849_stack (x0 := x0) (x2 := x2) (R := R)) (metaMorphoV1_1Creation_block_14849_memory (mem := mem)) (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((29) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 80167465652159884487584418398737133515478493586045375474096367959472086682926) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14893)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14849_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14849) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (metaMorphoV1_1Creation_block_14849_stack (x0 := x0) (x2 := x2) (R := R)) (metaMorphoV1_1Creation_block_14849_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14849 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14893. -/
theorem metaMorphoV1_1Creation_block_14893_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11023) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11023) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11023) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 11023) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11023)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14893_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11023) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11023) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14893_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14893. -/
theorem metaMorphoV1_1Creation_block_14893_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14901) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11023) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14901)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14893_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14893) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14901) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14893_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14901`. -/
def metaMorphoV1_1Creation_block_14901_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2379) :: ((UInt256.ofNat 32) + (x2 + x1)) :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14901. -/
theorem metaMorphoV1_1Creation_block_14901 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 4643) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14901) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 4643) (metaMorphoV1_1Creation_block_14901_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((36))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2379) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 4643) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 4643) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4643)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14901_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 4643) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14901) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 4643) (metaMorphoV1_1Creation_block_14901_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14901 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14917`. -/
def metaMorphoV1_1Creation_block_14917_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x1 + (UInt256.ofNat 32)) :: x2 :: (x3 + (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_14917`. -/
def metaMorphoV1_1Creation_block_14917_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x3 (⟨0⟩ : UInt256))).toByteArray.write 0 mem ((x2 + x1) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14917. -/
theorem metaMorphoV1_1Creation_block_14917 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10999) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14917) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10999) (metaMorphoV1_1Creation_block_14917_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14917_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3)) (M aw ((x2 + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 10999) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10999) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10999)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14917_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10999) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14917) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10999) (metaMorphoV1_1Creation_block_14917_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (metaMorphoV1_1Creation_block_14917_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_14917 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14943. -/
theorem metaMorphoV1_1Creation_block_14943_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14943) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14943_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14943) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14943_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14943. -/
theorem metaMorphoV1_1Creation_block_14943_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14943) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14949)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14943_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14943) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14943_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14949. -/
theorem metaMorphoV1_1Creation_block_14949_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14949_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14949_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14949. -/
theorem metaMorphoV1_1Creation_block_14949_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14960) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14960)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14949_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14949) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14960) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14949_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14960`. -/
def metaMorphoV1_1Creation_block_14960_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 11075) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14960. -/
theorem metaMorphoV1_1Creation_block_14960 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12247) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14960) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12247) (metaMorphoV1_1Creation_block_14960_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11075) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12247) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12247) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12247)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14960_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 12247) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14960) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12247) (metaMorphoV1_1Creation_block_14960_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14960 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14969. -/
theorem metaMorphoV1_1Creation_block_14969 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14969) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 σ ((x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat x3.toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14980`. -/
def metaMorphoV1_1Creation_block_14980_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((UInt256.land (UInt256.lnot (UInt256.ofNat 31)) ((UInt256.ofNat 31) + (memLoad x0 mem))) + x1) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_14980`. -/
def metaMorphoV1_1Creation_block_14980_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32).write ((UInt256.ofNat 32) + x0).toNat ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat (memLoad x0 mem).toNat) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14980. -/
theorem metaMorphoV1_1Creation_block_14980 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14980) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x2 (metaMorphoV1_1Creation_block_14980_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_14980_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (Mmcopy (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((98) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (mcopyExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) + (3 + 3 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (Mmcopy (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMcopy r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := RD.genMstore r23 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r33 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14980_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14980) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x2 (metaMorphoV1_1Creation_block_14980_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1Creation_block_14980_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14980 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15016. -/
theorem metaMorphoV1_1Creation_block_15016_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15016) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_15016_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15016) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_15016_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
