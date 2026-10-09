import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.CompoundIII.Comet.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace cometWithExtendedAssetListCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10218`. -/
def cometWithExtendedAssetListCreation_block_10218_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 128)) :: (UInt256.ofNat 7409) :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `cometWithExtendedAssetListCreation_block_10218`. -/
def cometWithExtendedAssetListCreation_block_10218_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10218. -/
theorem cometWithExtendedAssetListCreation_block_10218 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10218) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10218_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10218_memory (mem := mem) (x0 := x0) (x4 := x4)) (M aw (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 7409) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7126) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7126) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7126)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10218_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10218) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10218_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10218_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10218 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10235`. -/
def cometWithExtendedAssetListCreation_block_10235_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 160)) :: (UInt256.ofNat 7426) :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `cometWithExtendedAssetListCreation_block_10235`. -/
def cometWithExtendedAssetListCreation_block_10235_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10235. -/
theorem cometWithExtendedAssetListCreation_block_10235 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10235) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10235_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10235_memory (mem := mem) (x0 := x0) (x4 := x4)) (M aw (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 7426) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7126) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7126) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7126)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10235_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10235) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10235_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10235_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10235 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10252`. -/
def cometWithExtendedAssetListCreation_block_10252_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 192)) :: (UInt256.ofNat 7443) :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `cometWithExtendedAssetListCreation_block_10252`. -/
def cometWithExtendedAssetListCreation_block_10252_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10252. -/
theorem cometWithExtendedAssetListCreation_block_10252 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10252) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10252_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10252_memory (mem := mem) (x0 := x0) (x4 := x4)) (M aw (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 7443) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7126) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7126) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7126)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10252_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7126) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10252) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7126) (cometWithExtendedAssetListCreation_block_10252_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10252_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10252 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10269`. -/
def cometWithExtendedAssetListCreation_block_10269_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + x2) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `cometWithExtendedAssetListCreation_block_10269`. -/
def cometWithExtendedAssetListCreation_block_10269_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10269. -/
theorem cometWithExtendedAssetListCreation_block_10269 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7146) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10269) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7146) (cometWithExtendedAssetListCreation_block_10269_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10269_memory (mem := mem) (x0 := x0) (x4 := x4)) (M aw (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7146) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7146) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7146)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10269_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7146) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10269) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7146) (cometWithExtendedAssetListCreation_block_10269_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (cometWithExtendedAssetListCreation_block_10269_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10269 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10280`. -/
def cometWithExtendedAssetListCreation_block_10280_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Final memory for bytecode block summary `cometWithExtendedAssetListCreation_block_10280`. -/
def cometWithExtendedAssetListCreation_block_10280_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10280. -/
theorem cometWithExtendedAssetListCreation_block_10280 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10280) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_10280_stack (x1 := x1) (R := R)) (cometWithExtendedAssetListCreation_block_10280_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw (x1 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10280_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10280) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_10280_stack (x1 := x1) (R := R)) (cometWithExtendedAssetListCreation_block_10280_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10280 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10288`. -/
def cometWithExtendedAssetListCreation_block_10288_stack {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10288. -/
theorem cometWithExtendedAssetListCreation_block_10288 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7297) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10288) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7297) (cometWithExtendedAssetListCreation_block_10288_stack (rdata := rdata) (R := R)) mem aw rdata σ (k + 5) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7297) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7297) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7297)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10288_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7297) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10288) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7297) (cometWithExtendedAssetListCreation_block_10288_stack (rdata := rdata) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10288 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10295`. -/
def cometWithExtendedAssetListCreation_block_10295_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 7477) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10295. -/
theorem cometWithExtendedAssetListCreation_block_10295 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7166) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10295) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7166) (cometWithExtendedAssetListCreation_block_10295_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7477) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7166) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7166) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7166)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10295_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7166) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10295) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7166) (cometWithExtendedAssetListCreation_block_10295_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10295 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10303. -/
theorem cometWithExtendedAssetListCreation_block_10303 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7272) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10303) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7272) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7272) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7272) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7272)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10303_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7272) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10303) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7272) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10303 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10308`. -/
def cometWithExtendedAssetListCreation_block_10308_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 7491) :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10308. -/
theorem cometWithExtendedAssetListCreation_block_10308 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7039) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10308) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7039) (cometWithExtendedAssetListCreation_block_10308_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7491) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7039) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7039) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7039)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10308_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7039) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10308) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7039) (cometWithExtendedAssetListCreation_block_10308_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10308 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10317`. -/
def cometWithExtendedAssetListCreation_block_10317_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x2 :: x1 :: (UInt256.land (UInt256.ofNat 0) (UInt256.ofNat 255)) :: (UInt256.ofNat 255) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10317. -/
theorem cometWithExtendedAssetListCreation_block_10317 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10317) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (cometWithExtendedAssetListCreation_block_10317_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((27))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 0) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10361)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10317_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10317) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (cometWithExtendedAssetListCreation_block_10317_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10317 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10361. -/
theorem cometWithExtendedAssetListCreation_block_10361_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x0 x4) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7562) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7562) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7562) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7562) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7562)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10361_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x0 x4) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7562) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7562) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10361_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10361. -/
theorem cometWithExtendedAssetListCreation_block_10361_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x0 x4) x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10371) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7562) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10371)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10361_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x0 x4) x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10361) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10371) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10361_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10371. -/
theorem cometWithExtendedAssetListCreation_block_10371 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10371) R mem aw rdata σ k C)
    : RDrev (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 910185221) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10388`. -/
def cometWithExtendedAssetListCreation_block_10388_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 7571) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10388. -/
theorem cometWithExtendedAssetListCreation_block_10388 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7179) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10388) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7179) (cometWithExtendedAssetListCreation_block_10388_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7571) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7179) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7179) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7179)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10388_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7179) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10388) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7179) (cometWithExtendedAssetListCreation_block_10388_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10388 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10397. -/
theorem cometWithExtendedAssetListCreation_block_10397_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7605) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10397) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7605) (x0 :: x1 :: x2 :: R) mem (M aw (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7605) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7605) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7605)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10397_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7605) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10397) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7605) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10397_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10397. -/
theorem cometWithExtendedAssetListCreation_block_10397_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10397) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10421) (x0 :: x1 :: x2 :: R) mem (M aw (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7605) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10421)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10397_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10397) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10421) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10397_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10421`. -/
def cometWithExtendedAssetListCreation_block_10421_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x5 ((UInt256.ofNat 1) + x1)) :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10421. -/
theorem cometWithExtendedAssetListCreation_block_10421 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7535) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10421) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7535) (cometWithExtendedAssetListCreation_block_10421_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 7535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7535) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7535)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10421_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7535) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10421) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7535) (cometWithExtendedAssetListCreation_block_10421_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10421 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_10431`. -/
def cometWithExtendedAssetListCreation_block_10431_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10431. -/
theorem cometWithExtendedAssetListCreation_block_10431 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10431) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x3 (cometWithExtendedAssetListCreation_block_10431_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x3 hvalid) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10431_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10431) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x3 (cometWithExtendedAssetListCreation_block_10431_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10431 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10440. -/
theorem cometWithExtendedAssetListCreation_block_10440_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7637) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10440) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7637) R mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 40) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.timestamp (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7637) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7637) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7637)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10440_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7637) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10440) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7637) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10440_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10440. -/
theorem cometWithExtendedAssetListCreation_block_10440_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10440) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10453) R mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 40) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.timestamp (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7637) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10453)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_10440_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10440) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10453) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_10440_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListCreationBlocks
