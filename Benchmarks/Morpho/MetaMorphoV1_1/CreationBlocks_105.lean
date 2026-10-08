import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23137`. -/
def metaMorphoV1_1Creation_block_23137_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 19252) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 23137. -/
theorem metaMorphoV1_1Creation_block_23137 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23137) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23137_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 19252) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 19213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19213)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23137_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23137) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23137_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23137 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23146. -/
theorem metaMorphoV1_1Creation_block_23146_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19261) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23146) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19261) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19261) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 19261) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19261)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23146_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19261) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23146) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19261) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23146_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23146. -/
theorem metaMorphoV1_1Creation_block_23146_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23146) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23152) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19261) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23152)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23146_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23146) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23152) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23146_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23152`. -/
def metaMorphoV1_1Creation_block_23152_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23152. -/
theorem metaMorphoV1_1Creation_block_23152 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23152) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x2 (metaMorphoV1_1Creation_block_23152_stack (R := R)) mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23152_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23152) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x2 (metaMorphoV1_1Creation_block_23152_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23152 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23155`. -/
def metaMorphoV1_1Creation_block_23155_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 19270) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 23155. -/
theorem metaMorphoV1_1Creation_block_23155 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23155) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23155_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 19270) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 19213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19213)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23155_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23155) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23155_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23155 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23164. -/
theorem metaMorphoV1_1Creation_block_23164_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19293) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23164) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19293) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19293) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 19293) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19293)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23164_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19293) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23164) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19293) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23164_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23164. -/
theorem metaMorphoV1_1Creation_block_23164_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23164) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23173) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19293) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23173)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23164_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23164) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23173) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23164_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23173. -/
theorem metaMorphoV1_1Creation_block_23173 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23173) R mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.push4 (UInt256.ofNat 4131778271) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23187`. -/
def metaMorphoV1_1Creation_block_23187_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 19302) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 23187. -/
theorem metaMorphoV1_1Creation_block_23187 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23187) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23187_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 19302) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 19213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19213)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23187_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23187) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23187_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23187 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23196. -/
theorem metaMorphoV1_1Creation_block_23196_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23196) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19329) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19329) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 19329) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19329)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23196_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23196) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19329) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23196_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23196. -/
theorem metaMorphoV1_1Creation_block_23196_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23196) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23205) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19329) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23205)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23196_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23196) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23205) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23196_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23205. -/
theorem metaMorphoV1_1Creation_block_23205 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23205) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4242970871) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23223`. -/
def metaMorphoV1_1Creation_block_23223_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 19341) :: x0 :: (UInt256.ofNat 3) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23223. -/
theorem metaMorphoV1_1Creation_block_23223 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23223) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23223_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19341) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 19213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19213)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23223_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19213) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23223) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19213) (metaMorphoV1_1Creation_block_23223_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23223 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23235_taken`. -/
def metaMorphoV1_1Creation_block_23235_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23235. -/
theorem metaMorphoV1_1Creation_block_23235_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19349) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23235) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19349) (metaMorphoV1_1Creation_block_23235_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19349) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 19349) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19349)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23235_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19349) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23235) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19349) (metaMorphoV1_1Creation_block_23235_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23235_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23235_fallthrough`. -/
def metaMorphoV1_1Creation_block_23235_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23235. -/
theorem metaMorphoV1_1Creation_block_23235_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23235) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23241) (metaMorphoV1_1Creation_block_23235_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19349) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23241)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23235_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23235) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23241) (metaMorphoV1_1Creation_block_23235_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23235_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23241`. -/
def metaMorphoV1_1Creation_block_23241_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23241. -/
theorem metaMorphoV1_1Creation_block_23241 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23241) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x1 (metaMorphoV1_1Creation_block_23241_stack (R := R)) mem aw rdata σ (k + 2) (C + ((10))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r2 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23241_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23241) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 x1 (metaMorphoV1_1Creation_block_23241_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23241 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 23243. -/
theorem metaMorphoV1_1Creation_block_23243 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23243) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 904065923) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 226) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_23261`. -/
def metaMorphoV1_1Creation_block_23261_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 64) :: (UInt256.ofNat 19381) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23261. -/
theorem metaMorphoV1_1Creation_block_23261 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23261) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11329) (metaMorphoV1_1Creation_block_23261_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19381) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11329) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11329) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11329)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23261_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 11329) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23261) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11329) (metaMorphoV1_1Creation_block_23261_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23261 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_23275_taken`. -/
def metaMorphoV1_1Creation_block_23275_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 156113407705867659558375029309965657412092893529) (UInt256.ofNat 98)).toByteArray.write 0 ((UInt256.ofNat 20).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 23275. -/
theorem metaMorphoV1_1Creation_block_23275_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19441) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23275) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19441) (x0 :: x1 :: R) (metaMorphoV1_1Creation_block_23275_taken_memory (mem := mem) (x0 := x0)) (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 20) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 156113407705867659558375029309965657412092893529) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 19441) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 19441) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19441)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23275_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 19441) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23275) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 19441) (x0 :: x1 :: R) (metaMorphoV1_1Creation_block_23275_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23275_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1Creation_block_23275_fallthrough`. -/
def metaMorphoV1_1Creation_block_23275_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 156113407705867659558375029309965657412092893529) (UInt256.ofNat 98)).toByteArray.write 0 ((UInt256.ofNat 20).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 23275. -/
theorem metaMorphoV1_1Creation_block_23275_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23275) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23323) (x0 :: x1 :: R) (metaMorphoV1_1Creation_block_23275_fallthrough_memory (mem := mem) (x0 := x0)) (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23666 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 20) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 156113407705867659558375029309965657412092893529) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 98) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 19441) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23323)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_23275_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23275) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23323) (x0 :: x1 :: R) (metaMorphoV1_1Creation_block_23275_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_23275_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
