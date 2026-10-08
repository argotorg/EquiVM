import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MorphoBlue.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace morphoCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 535. -/
theorem morphoCreation_block_535_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1183860800) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 9265) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9265) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1183860800) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 9265) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 9265) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9265)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_535_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1183860800) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 9265) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9265) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_535_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 535. -/
theorem morphoCreation_block_535_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1183860800) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1183860800) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 9265) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 546)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_535_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1183860800) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_535_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 546. -/
theorem morphoCreation_block_546_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1301850427) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8981) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8981) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1301850427) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8981) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 8981) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8981)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_546_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1301850427) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8981) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8981) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_546_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 546. -/
theorem morphoCreation_block_546_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1301850427) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1301850427) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8981) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 557)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_546_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1301850427) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 546) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_546_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 557. -/
theorem morphoCreation_block_557_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1356385611) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8321) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8321) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1356385611) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8321) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 8321) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8321)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_557_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1356385611) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8321) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8321) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_557_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 557. -/
theorem morphoCreation_block_557_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1356385611) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1356385611) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8321) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 568)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_557_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1356385611) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 557) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_557_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 568. -/
theorem morphoCreation_block_568_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1516565790) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8105) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8105) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1516565790) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8105) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 8105) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8105)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_568_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1516565790) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 8105) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 8105) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_568_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 568. -/
theorem morphoCreation_block_568_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1516565790) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1516565790) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8105) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 579)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_568_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1516565790) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_568_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 579. -/
theorem morphoCreation_block_579_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1546381897) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7496) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7496) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1546381897) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7496) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7496) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7496)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_579_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1546381897) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7496) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7496) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_579_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 579. -/
theorem morphoCreation_block_579_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1546381897) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1546381897) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7496) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 590)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_579_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1546381897) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 579) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_579_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem morphoCreation_block_590_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1549853594) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7351) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7351) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1549853594) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7351) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7351) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7351)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_590_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1549853594) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7351) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7351) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_590_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem morphoCreation_block_590_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1549853594) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1549853594) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7351) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 601)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_590_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1549853594) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 590) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_590_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 601. -/
theorem morphoCreation_block_601_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1709485470) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7223) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7223) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1709485470) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7223) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7223) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7223)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_601_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1709485470) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7223) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7223) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_601_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 601. -/
theorem morphoCreation_block_601_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1709485470) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1709485470) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7223) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 612)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_601_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1709485470) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 601) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_601_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 612. -/
theorem morphoCreation_block_612_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1890489042) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7124) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7124) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1890489042) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7124) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7124) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7124)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_612_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1890489042) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 7124) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7124) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_612_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 612. -/
theorem morphoCreation_block_612_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1890489042) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1890489042) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7124) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 623)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_612_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1890489042) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 612) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_612_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 623. -/
theorem morphoCreation_block_623_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2005190277) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 6760) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 6760) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2005190277) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6760) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 6760) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6760)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_623_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2005190277) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 6760) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 6760) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_623_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 623. -/
theorem morphoCreation_block_623_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2005190277) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2005190277) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6760) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 634)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_623_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2005190277) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 623) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_623_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 634. -/
theorem morphoCreation_block_634_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2154373519) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5759) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5759) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2154373519) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5759) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 5759) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5759)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_634_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2154373519) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5759) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5759) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_634_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 634. -/
theorem morphoCreation_block_634_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2154373519) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 645) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2154373519) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5759) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 645)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_634_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2154373519) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 634) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 645) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_634_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end morphoCreationBlocks
