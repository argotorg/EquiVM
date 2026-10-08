import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.CompoundIII.Comet.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace cometWithExtendedAssetListCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 13413. -/
theorem cometWithExtendedAssetListCreation_block_13413 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 2959) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2959) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2959) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2959)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13413_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 2959) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2959) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13413 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13418`. -/
def cometWithExtendedAssetListCreation_block_13418_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13418. -/
theorem cometWithExtendedAssetListCreation_block_13418 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11132) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13418) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11132) (cometWithExtendedAssetListCreation_block_13418_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11132) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11132) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11132)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13418_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11132) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13418) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11132) (cometWithExtendedAssetListCreation_block_13418_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13418 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13424. -/
theorem cometWithExtendedAssetListCreation_block_13424 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10129) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13424) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10129) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10129) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10129) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10129)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13424_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10129) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13424) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10129) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13424 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13429`. -/
def cometWithExtendedAssetListCreation_block_13429_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x8 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13429. -/
theorem cometWithExtendedAssetListCreation_block_13429 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10427) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10427) (cometWithExtendedAssetListCreation_block_13429_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 10427) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10427) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10427)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13429_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10427) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10427) (cometWithExtendedAssetListCreation_block_13429_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13429 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13438`. -/
def cometWithExtendedAssetListCreation_block_13438_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13438. -/
theorem cometWithExtendedAssetListCreation_block_13438 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13438) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x8 (cometWithExtendedAssetListCreation_block_13438_stack (R := R)) mem aw rdata σ (k + 12) (C + ((31))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x8 hvalid) (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13438_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13438) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x8 (cometWithExtendedAssetListCreation_block_13438_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13438 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13451`. -/
def cometWithExtendedAssetListCreation_block_13451_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13451. -/
theorem cometWithExtendedAssetListCreation_block_13451 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13451) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x3 (cometWithExtendedAssetListCreation_block_13451_stack (R := R)) mem aw rdata σ (k + 7) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x3 hvalid) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13451_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13451) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x3 (cometWithExtendedAssetListCreation_block_13451_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13451 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13459_taken`. -/
def cometWithExtendedAssetListCreation_block_13459_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.signextend (UInt256.ofNat 12) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13459. -/
theorem cometWithExtendedAssetListCreation_block_13459_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10658) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13459) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10658) (cometWithExtendedAssetListCreation_block_13459_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((46))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 103) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 10658) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 10658) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10658)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13459_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10658) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13459) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10658) (cometWithExtendedAssetListCreation_block_13459_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13459_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13459_fallthrough`. -/
def cometWithExtendedAssetListCreation_block_13459_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.signextend (UInt256.ofNat 12) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13459. -/
theorem cometWithExtendedAssetListCreation_block_13459_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13459) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13478) (cometWithExtendedAssetListCreation_block_13459_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((46))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 103) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 10658) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13478)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13459_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13459) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13478) (cometWithExtendedAssetListCreation_block_13459_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13459_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13478`. -/
def cometWithExtendedAssetListCreation_block_13478_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat 0) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13478. -/
theorem cometWithExtendedAssetListCreation_block_13478 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13478) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_13478_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13478_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13478) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_13478_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13478 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13484`. -/
def cometWithExtendedAssetListCreation_block_13484_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 10666) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13484. -/
theorem cometWithExtendedAssetListCreation_block_13484 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7730) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13484) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7730) (cometWithExtendedAssetListCreation_block_13484_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10666) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7730) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7730) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7730)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13484_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7730) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13484) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7730) (cometWithExtendedAssetListCreation_block_13484_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13484 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13492. -/
theorem cometWithExtendedAssetListCreation_block_13492 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10652) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13492) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10652) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10652) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10652) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10652)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13492_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10652) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13492) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10652) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13492 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13497. -/
theorem cometWithExtendedAssetListCreation_block_13497_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10658) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13497) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10658) (x0 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10658) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 10658) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10658)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13497_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10658) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13497) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10658) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13497_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13497. -/
theorem cometWithExtendedAssetListCreation_block_13497_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13497) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13509) (x0 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10658) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13509)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13497_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x0 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13497) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13509) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13497_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13509`. -/
def cometWithExtendedAssetListCreation_block_13509_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat 0) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13509. -/
theorem cometWithExtendedAssetListCreation_block_13509 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13509) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_13509_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13509_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13509) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_13509_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13509 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13514. -/
theorem cometWithExtendedAssetListCreation_block_13514_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10752) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13514) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10752) (x0 :: R) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 10752) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 10752) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10752)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13514_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10752) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13514) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10752) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13514_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13514. -/
theorem cometWithExtendedAssetListCreation_block_13514_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13514) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13527) (x0 :: R) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 10752) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13527)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13514_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) x0) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13514) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13527) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13514_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13527`. -/
def cometWithExtendedAssetListCreation_block_13527_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1)) x0) :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) :: (UInt256.ofNat 10746) :: (UInt256.ofNat 1000000000000000) :: (UInt256.ofNat 2425) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13527. -/
theorem cometWithExtendedAssetListCreation_block_13527 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7799) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13527) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7799) (cometWithExtendedAssetListCreation_block_13527_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2425) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 1000000000000000) (width := 7) (op := .PUSH7) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10746) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 104) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 7799) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 7799) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7799)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13527_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 7799) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13527) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7799) (cometWithExtendedAssetListCreation_block_13527_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetListCreation_block_13527 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13572`. -/
def cometWithExtendedAssetListCreation_block_13572_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13572. -/
theorem cometWithExtendedAssetListCreation_block_13572 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10129) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13572) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10129) (cometWithExtendedAssetListCreation_block_13572_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10129) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10129) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10129)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13572_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10129) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13572) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10129) (cometWithExtendedAssetListCreation_block_13572_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13572 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13578`. -/
def cometWithExtendedAssetListCreation_block_13578_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 10785) :: (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))) (UInt256.ofNat 64)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) :: (UInt256.ofNat 10598) :: (UInt256.ofNat 10800) :: (UInt256.ofNat 2425) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13578. -/
theorem cometWithExtendedAssetListCreation_block_13578 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10633) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13578) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10633) (cometWithExtendedAssetListCreation_block_13578_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10800) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10598) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2425) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 10785) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 10633) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10633) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10633)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13578_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 10633) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13578) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10633) (cometWithExtendedAssetListCreation_block_13578_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetListCreation_block_13578 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_13611`. -/
def cometWithExtendedAssetListCreation_block_13611_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1)) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13611. -/
theorem cometWithExtendedAssetListCreation_block_13611 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 9318) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13611) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9318) (cometWithExtendedAssetListCreation_block_13611_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 104) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 9318) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 9318) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9318)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_13611_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 9318) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13611) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9318) (cometWithExtendedAssetListCreation_block_13611_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_13611 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListCreationBlocks
