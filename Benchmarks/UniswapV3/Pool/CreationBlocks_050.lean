import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV3.Pool.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace uniswapV3PoolCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15521_taken`. -/
def uniswapV3PoolCreation_block_15521_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4)) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15521. -/
theorem uniswapV3PoolCreation_block_15521_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14968) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15521) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14968) (uniswapV3PoolCreation_block_15521_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14968) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14968) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14968)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15521_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14968) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15521) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14968) (uniswapV3PoolCreation_block_15521_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15521_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15521_fallthrough`. -/
def uniswapV3PoolCreation_block_15521_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4)) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15521. -/
theorem uniswapV3PoolCreation_block_15521_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15521) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15539) (uniswapV3PoolCreation_block_15521_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14968) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15539)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15521_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.land (UInt256.ofNat 65535) x4))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15521) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15539) (uniswapV3PoolCreation_block_15521_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15521_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15539`. -/
def uniswapV3PoolCreation_block_15539_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.land (UInt256.ofNat 65535) x9) (UInt256.land (UInt256.ofNat 65535) (UInt256.sub x5 (UInt256.ofNat 1)))) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15539. -/
theorem uniswapV3PoolCreation_block_15539 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (uniswapV3PoolCreation_block_15539_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ (k + 10) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15554)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15539_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (uniswapV3PoolCreation_block_15539_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15539 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15554_taken`. -/
def uniswapV3PoolCreation_block_15554_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15554. -/
theorem uniswapV3PoolCreation_block_15554_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14981) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14981) (uniswapV3PoolCreation_block_15554_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14981) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14981) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14981)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15554_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14981) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14981) (uniswapV3PoolCreation_block_15554_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15554_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15554_fallthrough`. -/
def uniswapV3PoolCreation_block_15554_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15554. -/
theorem uniswapV3PoolCreation_block_15554_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15560) (uniswapV3PoolCreation_block_15554_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14981) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15560)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15554_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15554) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15560) (uniswapV3PoolCreation_block_15554_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15554_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15560`. -/
def uniswapV3PoolCreation_block_15560_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15560. -/
theorem uniswapV3PoolCreation_block_15560 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14985) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15560) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14985) (uniswapV3PoolCreation_block_15560_stack (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14985) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 14985) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14985)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15560_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 14985) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15560) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14985) (uniswapV3PoolCreation_block_15560_stack (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15560 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15567`. -/
def uniswapV3PoolCreation_block_15567_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x4 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15567. -/
theorem uniswapV3PoolCreation_block_15567 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15567) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (uniswapV3PoolCreation_block_15567_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 4) (C + ((9))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15571)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15567_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15567) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (uniswapV3PoolCreation_block_15567_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15567 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15571_taken`. -/
def uniswapV3PoolCreation_block_15571_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 65535) ((UInt256.ofNat 1) + x8)) :: (UInt256.land (UInt256.ofNat 65535) x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15571. -/
theorem uniswapV3PoolCreation_block_15571_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 65535) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15005) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15005) (uniswapV3PoolCreation_block_15571_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 15005) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 15005) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15005)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15571_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 65535) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15005) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15005) (uniswapV3PoolCreation_block_15571_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15571_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15571_fallthrough`. -/
def uniswapV3PoolCreation_block_15571_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 65535) ((UInt256.ofNat 1) + x8)) :: (UInt256.land (UInt256.ofNat 65535) x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15571. -/
theorem uniswapV3PoolCreation_block_15571_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 65535) x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15590) (uniswapV3PoolCreation_block_15571_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 15005) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15590)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15571_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 65535) x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15590) (uniswapV3PoolCreation_block_15571_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15571_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15590. -/
theorem uniswapV3PoolCreation_block_15590 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15590) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15591`. -/
def uniswapV3PoolCreation_block_15591_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: x8 :: x9 :: x2 :: (UInt256.ofNat 15020) :: x2 :: x3 :: (UInt256.mod x0 x1) :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15591. -/
theorem uniswapV3PoolCreation_block_15591 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18466) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15591) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18466) (uniswapV3PoolCreation_block_15591_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.mod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 15020) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 18466) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18466) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18466)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15591_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18466) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15591) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18466) (uniswapV3PoolCreation_block_15591_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15591 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15606_taken`. -/
def uniswapV3PoolCreation_block_15606_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 65535) x3) :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15606. -/
theorem uniswapV3PoolCreation_block_15606_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.ofNat 65535)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15037) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15606) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15037) (uniswapV3PoolCreation_block_15606_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 15037) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 15037) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15037)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15606_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.ofNat 65535)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15037) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15606) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15037) (uniswapV3PoolCreation_block_15606_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15606_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15606_fallthrough`. -/
def uniswapV3PoolCreation_block_15606_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 65535) x3) :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15606. -/
theorem uniswapV3PoolCreation_block_15606_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.ofNat 65535)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15606) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15622) (uniswapV3PoolCreation_block_15606_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 15037) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15622)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15606_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land (UInt256.ofNat 65535) x3) (UInt256.ofNat 65535)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15606) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15622) (uniswapV3PoolCreation_block_15606_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15606_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15622. -/
theorem uniswapV3PoolCreation_block_15622 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15622) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15623`. -/
def uniswapV3PoolCreation_block_15623_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + x0) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295))) (UInt256.land (memLoad x2 mem) (UInt256.ofNat 4294967295))) :: (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88)) (UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) :: (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248)) (UInt256.isZero (UInt256.isZero (memLoad (x2 + (UInt256.ofNat 96)) mem)))) :: (UInt256.ofNat 115339776388732929035197660848497720713218148788040715071188274165450943758335) :: (UInt256.mul (UInt256.ofNat 4294967296) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (memLoad (x2 + (UInt256.ofNat 32)) mem)))) :: (x1 + x0) :: (UInt256.lnot (UInt256.ofNat 309485009821345064429813760)) :: (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15623. -/
theorem uniswapV3PoolCreation_block_15623 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15623) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15792) (uniswapV3PoolCreation_block_15623_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMload r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := RD.genMload r19 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 248) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.pushConst (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655) (width := 31) (op := .PUSH31) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.pushConst (UInt256.ofNat 115339776388732929035197660848497720713218148788040715071188274165450943758335) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 6) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.pushConst (UInt256.ofNat 72057594037927935) (width := 7) (op := .PUSH7) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.pushConst (UInt256.ofNat 4294967296) (width := 5) (op := .PUSH5) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.pushConst (UInt256.ofNat 309485009821345064429813760) (width := 11) (op := .PUSH11) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15792)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15623_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15623) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15792) (uniswapV3PoolCreation_block_15623_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3PoolCreation_block_15623 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15792`. -/
def uniswapV3PoolCreation_block_15792_stack {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15792. -/
theorem uniswapV3PoolCreation_block_15792 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x18 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15792) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x18 (uniswapV3PoolCreation_block_15792_stack (x9 := x9) (x10 := x10) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x0 x6) x4) x3) x1) x7) x2)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x18 hvalid) (by evm_ov)
  exact ⟨_, _, r32⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15792_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x18 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15792) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x18 (uniswapV3PoolCreation_block_15792_stack (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x0 x6) x4) x3) x1) x7) x2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3PoolCreation_block_15792 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15824`. -/
def uniswapV3PoolCreation_block_15824_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) :: (memLoad (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) ((UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)))).toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)).toNat 32)) :: (memLoad (UInt256.ofNat 64) ((UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)))).toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `uniswapV3PoolCreation_block_15824`. -/
def uniswapV3PoolCreation_block_15824_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32)))).toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toByteArray.write 0 (((UInt256.ofNat 68) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)))).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)).toNat 32) (UInt256.ofNat 64).toNat 32) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15824. -/
theorem uniswapV3PoolCreation_block_15824 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15824) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15905) (uniswapV3PoolCreation_block_15824_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (uniswapV3PoolCreation_block_15824_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((190) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMstore r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := RD.genMstore r22 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := RD.genMstore r32 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 100) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := RD.genMstore r38 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := RD.genMload r43 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.push4 (UInt256.ofNat 2835717307) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := RD.genMstore r55 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := RD.genMload r57 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := RD.genMload r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15905)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15824_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15824) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15905) (uniswapV3PoolCreation_block_15824_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (uniswapV3PoolCreation_block_15824_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15824 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_15905`. -/
def uniswapV3PoolCreation_block_15905_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x3 :: x2 :: x2 :: x1 :: x3 :: x3 :: x0 :: (UInt256.land x9 x4) :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15905. -/
theorem uniswapV3PoolCreation_block_15905 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15905) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (uniswapV3PoolCreation_block_15905_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ (k + 12) (C + ((36))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15917)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15905_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15905) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (uniswapV3PoolCreation_block_15905_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15905 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15917. -/
theorem uniswapV3PoolCreation_block_15917_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15362) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15362) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 15362) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 15362) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15362)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15917_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 15362) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15362) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15917_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15917. -/
theorem uniswapV3PoolCreation_block_15917_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15926) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 15362) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15926)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_15917_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15917) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15926) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_15917_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolCreationBlocks
