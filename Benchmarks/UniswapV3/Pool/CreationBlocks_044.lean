import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV3.Pool.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace uniswapV3PoolCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13354`. -/
def uniswapV3PoolCreation_block_13354_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1) :: x9 :: x6 :: x11 :: (UInt256.ofNat 12780) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13354. -/
theorem uniswapV3PoolCreation_block_13354 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18002) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13354) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18002) (uniswapV3PoolCreation_block_13354_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 12780) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 18002) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18002) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18002)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13354_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18002) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13354) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18002) (uniswapV3PoolCreation_block_13354_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13354 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13366. -/
theorem uniswapV3PoolCreation_block_13366 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12787) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13366) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12787) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12787) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12787) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12787)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13366_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12787) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13366) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12787) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13366 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13371`. -/
def uniswapV3PoolCreation_block_13371_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13371. -/
theorem uniswapV3PoolCreation_block_13371 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13371) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (uniswapV3PoolCreation_block_13371_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13373)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13371_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13371) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (uniswapV3PoolCreation_block_13371_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13371 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13373_taken`. -/
def uniswapV3PoolCreation_block_13373_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13373. -/
theorem uniswapV3PoolCreation_block_13373_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12800) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12800) (uniswapV3PoolCreation_block_13373_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 12800) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12800) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12800)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13373_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12800) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12800) (uniswapV3PoolCreation_block_13373_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13373_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13373_fallthrough`. -/
def uniswapV3PoolCreation_block_13373_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13373. -/
theorem uniswapV3PoolCreation_block_13373_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13383) (uniswapV3PoolCreation_block_13373_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 12800) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13383)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13373_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13373) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13383) (uniswapV3PoolCreation_block_13373_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13373_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13383`. -/
def uniswapV3PoolCreation_block_13383_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x2) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13383. -/
theorem uniswapV3PoolCreation_block_13383 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13383) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (uniswapV3PoolCreation_block_13383_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 3) (C + ((8))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13386)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13383_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13383) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (uniswapV3PoolCreation_block_13383_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13383 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13386_taken`. -/
def uniswapV3PoolCreation_block_13386_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 13386. -/
theorem uniswapV3PoolCreation_block_13386_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12822) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12822) (uniswapV3PoolCreation_block_13386_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12822) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12822) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12822)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13386_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12822) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12822) (uniswapV3PoolCreation_block_13386_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13386_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13386_fallthrough`. -/
def uniswapV3PoolCreation_block_13386_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 13386. -/
theorem uniswapV3PoolCreation_block_13386_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13391) (uniswapV3PoolCreation_block_13386_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12822) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13391)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13386_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13386) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13391) (uniswapV3PoolCreation_block_13386_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13386_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13391`. -/
def uniswapV3PoolCreation_block_13391_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x9 :: x6 :: x11 :: (UInt256.ofNat 12817) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13391. -/
theorem uniswapV3PoolCreation_block_13391 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18125) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13391) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18125) (uniswapV3PoolCreation_block_13391_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 12817) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 18125) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18125) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18125)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13391_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18125) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13391) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18125) (uniswapV3PoolCreation_block_13391_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13391 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13403. -/
theorem uniswapV3PoolCreation_block_13403 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12824) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13403) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12824) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12824) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12824) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12824)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13403_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12824) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13403) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12824) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13403 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13408`. -/
def uniswapV3PoolCreation_block_13408_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13408. -/
theorem uniswapV3PoolCreation_block_13408 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13408) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13410) (uniswapV3PoolCreation_block_13408_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13410)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13408_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13408) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13410) (uniswapV3PoolCreation_block_13408_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13408 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13410`. -/
def uniswapV3PoolCreation_block_13410_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13410. -/
theorem uniswapV3PoolCreation_block_13410 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13410) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (uniswapV3PoolCreation_block_13410_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 3) (C + ((6))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13413)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13410_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13410) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (uniswapV3PoolCreation_block_13410_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13410 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13413_taken`. -/
def uniswapV3PoolCreation_block_13413_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13413. -/
theorem uniswapV3PoolCreation_block_13413_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12843) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12843) (uniswapV3PoolCreation_block_13413_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12843) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12843) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12843)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13413_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12843) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12843) (uniswapV3PoolCreation_block_13413_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13413_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13413_fallthrough`. -/
def uniswapV3PoolCreation_block_13413_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13413. -/
theorem uniswapV3PoolCreation_block_13413_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13422) (uniswapV3PoolCreation_block_13413_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12843) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13422)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13413_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13413) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13422) (uniswapV3PoolCreation_block_13413_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13413_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13422`. -/
def uniswapV3PoolCreation_block_13422_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt x5 (UInt256.sub (UInt256.ofNat 0) x9)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13422. -/
theorem uniswapV3PoolCreation_block_13422 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13422) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (uniswapV3PoolCreation_block_13422_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ (k + 6) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13429)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13422_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13422) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (uniswapV3PoolCreation_block_13422_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13422 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13429_taken`. -/
def uniswapV3PoolCreation_block_13429_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 13429. -/
theorem uniswapV3PoolCreation_block_13429_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12855) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12855) (uniswapV3PoolCreation_block_13429_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12855) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12855) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12855)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13429_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12855) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12855) (uniswapV3PoolCreation_block_13429_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13429_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13429_fallthrough`. -/
def uniswapV3PoolCreation_block_13429_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 13429. -/
theorem uniswapV3PoolCreation_block_13429_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13435) (uniswapV3PoolCreation_block_13429_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12855) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13435)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13429_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13429) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13435) (uniswapV3PoolCreation_block_13429_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13429_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13435`. -/
def uniswapV3PoolCreation_block_13435_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: (UInt256.sub (UInt256.ofNat 0) x8) :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13435. -/
theorem uniswapV3PoolCreation_block_13435 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13435) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (uniswapV3PoolCreation_block_13435_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 5) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13441)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13435_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13435) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (uniswapV3PoolCreation_block_13435_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13435 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13441_taken`. -/
def uniswapV3PoolCreation_block_13441_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13441. -/
theorem uniswapV3PoolCreation_block_13441_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12886) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12886) (uniswapV3PoolCreation_block_13441_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12886) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12886) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12886)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13441_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 12886) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12886) (uniswapV3PoolCreation_block_13441_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13441_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13441_fallthrough`. -/
def uniswapV3PoolCreation_block_13441_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13441. -/
theorem uniswapV3PoolCreation_block_13441_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13449) (uniswapV3PoolCreation_block_13441_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12886) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13449)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13441_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13449) (uniswapV3PoolCreation_block_13441_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13441_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolCreationBlocks
