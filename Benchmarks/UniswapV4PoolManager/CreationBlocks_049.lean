import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV4PoolManager.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 17128. -/
theorem poolManagerCreation_block_17128_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 65536)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17118) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17118) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 65536) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17118) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 17118) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17118)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17128_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 65536)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17118) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17118) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17128_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 17128. -/
theorem poolManagerCreation_block_17128_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 65536)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 65536) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17118) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17139)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17128_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 65536)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17128_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 17139. -/
theorem poolManagerCreation_block_17139_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 131072)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17091) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17091) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 131072) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17091) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 17091) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17091)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17139_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 131072)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17091) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17091) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17139_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 17139. -/
theorem poolManagerCreation_block_17139_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 131072)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 131072) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17091) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17150)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17139_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 131072)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17139) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17139_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 17150. -/
theorem poolManagerCreation_block_17150_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 262144)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17064) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17064) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 262144) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17064) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 17064) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17064)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17150_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 262144)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17064) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17064) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17150_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 17150. -/
theorem poolManagerCreation_block_17150_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 262144)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 262144) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 17064) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17161)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17150_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.ofNat 262144)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17150) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17150_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17161_taken`. -/
def poolManagerCreation_block_17161_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17161. -/
theorem poolManagerCreation_block_17161_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 524288) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17039) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17039) (poolManagerCreation_block_17161_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 524288) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 17039) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 17039) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17039)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17161_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 524288) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17039) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17039) (poolManagerCreation_block_17161_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17161_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17161_fallthrough`. -/
def poolManagerCreation_block_17161_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17161. -/
theorem poolManagerCreation_block_17161_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 524288) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (poolManagerCreation_block_17161_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 524288) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 17039) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17171)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17161_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 524288) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17161) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (poolManagerCreation_block_17161_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17161_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17171_taken`. -/
def poolManagerCreation_block_17171_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17171. -/
theorem poolManagerCreation_block_17171_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (⟨0⟩ : UInt256) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17000) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17000) (poolManagerCreation_block_17171_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 17000) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 17000) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17000)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17171_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (⟨0⟩ : UInt256) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 17000) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17000) (poolManagerCreation_block_17171_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17171_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17171_fallthrough`. -/
def poolManagerCreation_block_17171_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17171. -/
theorem poolManagerCreation_block_17171_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (⟨0⟩ : UInt256) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17178) (poolManagerCreation_block_17171_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 17000) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17178)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17171_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.slt (⟨0⟩ : UInt256) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17171) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17178) (poolManagerCreation_block_17171_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17171_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17178`. -/
def poolManagerCreation_block_17178_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (x0 + x1) (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17178. -/
theorem poolManagerCreation_block_17178 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17178) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x2 (poolManagerCreation_block_17178_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17178_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17178) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x2 (poolManagerCreation_block_17178_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17178 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17185`. -/
def poolManagerCreation_block_17185_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17185. -/
theorem poolManagerCreation_block_17185 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16993) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17185) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16993) (poolManagerCreation_block_17185_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 16993) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16993) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16993)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17185_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16993) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17185) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16993) (poolManagerCreation_block_17185_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17185 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17224`. -/
def poolManagerCreation_block_17224_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.shiftRight (UInt256.mul x1 (UInt256.ofNat 1404880482679654955896180642)) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17224. -/
theorem poolManagerCreation_block_17224 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16986) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17224) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16986) (poolManagerCreation_block_17224_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1404880482679654955896180642) (width := 12) (op := .PUSH12) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 16986) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16986) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16986)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17224_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16986) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17224) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16986) (poolManagerCreation_block_17224_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17224 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17249`. -/
def poolManagerCreation_block_17249_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul x2 (UInt256.ofNat 691415978906521570653435304214168)) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17249. -/
theorem poolManagerCreation_block_17249 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16976) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16976) (poolManagerCreation_block_17249_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 691415978906521570653435304214168) (width := 14) (op := .PUSH14) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 16976) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16976) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16976)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17249_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16976) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16976) (poolManagerCreation_block_17249_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17249 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17276`. -/
def poolManagerCreation_block_17276_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 485053260817066172746253684029974020) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17276. -/
theorem poolManagerCreation_block_17276 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16965) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17276) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16965) (poolManagerCreation_block_17276_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 485053260817066172746253684029974020) (width := 15) (op := .PUSH15) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16965) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16965) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16965)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17276_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16965) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17276) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16965) (poolManagerCreation_block_17276_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17276 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17303`. -/
def poolManagerCreation_block_17303_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 12847376061809297530290974190478138313) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17303. -/
theorem poolManagerCreation_block_17303 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16954) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17303) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16954) (poolManagerCreation_block_17303_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 12847376061809297530290974190478138313) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16954) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16954) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16954)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17303_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16954) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17303) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16954) (poolManagerCreation_block_17303_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17303 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17331`. -/
def poolManagerCreation_block_17331_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 66119101136024775622716233608466517926) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17331. -/
theorem poolManagerCreation_block_17331 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16943) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17331) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16943) (poolManagerCreation_block_17331_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 66119101136024775622716233608466517926) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16943) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16943) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16943)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17331_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16943) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17331) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16943) (poolManagerCreation_block_17331_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17331 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17359`. -/
def poolManagerCreation_block_17359_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 149997214084966997727330242082538205943) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17359. -/
theorem poolManagerCreation_block_17359 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16933) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17359) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16933) (poolManagerCreation_block_17359_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 149997214084966997727330242082538205943) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16933) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16933) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16933)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17359_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16933) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17359) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16933) (poolManagerCreation_block_17359_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17359 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17387`. -/
def poolManagerCreation_block_17387_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 225923453940442621947126027127485391333) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17387. -/
theorem poolManagerCreation_block_17387 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16923) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17387) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16923) (poolManagerCreation_block_17387_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 225923453940442621947126027127485391333) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16923) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16923) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16923)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17387_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16923) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17387) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16923) (poolManagerCreation_block_17387_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17387 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_17415`. -/
def poolManagerCreation_block_17415_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 277268403626896220162999269216087595045) x2) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17415. -/
theorem poolManagerCreation_block_17415 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16913) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17415) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16913) (poolManagerCreation_block_17415_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 277268403626896220162999269216087595045) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 16913) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 16913) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16913)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_17415_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 16913) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17415) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 16913) (poolManagerCreation_block_17415_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_17415 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end poolManagerCreationBlocks
