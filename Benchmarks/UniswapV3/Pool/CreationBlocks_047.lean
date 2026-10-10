import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV3.Pool.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace uniswapV3PoolCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13926`. -/
def uniswapV3PoolCreation_block_13926_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 64) + x0) mem) :: (memLoad ((UInt256.ofNat 32) + x0) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13926. -/
theorem uniswapV3PoolCreation_block_13926 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13926) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_13926_stack (mem := mem) (x0 := x0) (R := R)) mem (M (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((48) + (memExpansionCost aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 13584) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 13584) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13584)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13926_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13926) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_13926_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13926 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13946`. -/
def uniswapV3PoolCreation_block_13946_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: (UInt256.sub x7 x6) :: x7 :: x8 :: (UInt256.ofNat 13381) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.sub x7 x6) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13946. -/
theorem uniswapV3PoolCreation_block_13946 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18642) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13946) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18642) (uniswapV3PoolCreation_block_13946_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 16) (C + ((51))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13381) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 18642) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 18642) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18642)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13946_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 18642) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13946) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 18642) (uniswapV3PoolCreation_block_13946_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13946 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13967_taken`. -/
def uniswapV3PoolCreation_block_13967_taken_stack {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13967. -/
theorem uniswapV3PoolCreation_block_13967_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.ofNat 4294967295) x4) (UInt256.land (UInt256.ofNat 4294967295) (memLoad ((UInt256.ofNat 0) + x1) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13431) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13967) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13431) (uniswapV3PoolCreation_block_13967_taken_stack (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem (M aw ((UInt256.ofNat 0) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((57) + (memExpansionCost aw ((UInt256.ofNat 0) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 13431) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13431) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13431)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13967_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.ofNat 4294967295) x4) (UInt256.land (UInt256.ofNat 4294967295) (memLoad ((UInt256.ofNat 0) + x1) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13431) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13967) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13431) (uniswapV3PoolCreation_block_13967_taken_stack (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13967_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13967_fallthrough`. -/
def uniswapV3PoolCreation_block_13967_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13967. -/
theorem uniswapV3PoolCreation_block_13967_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.ofNat 4294967295) x4) (UInt256.land (UInt256.ofNat 4294967295) (memLoad ((UInt256.ofNat 0) + x1) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13967) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13996) (uniswapV3PoolCreation_block_13967_fallthrough_stack (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem (M aw ((UInt256.ofNat 0) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((57) + (memExpansionCost aw ((UInt256.ofNat 0) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 13431) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13996)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13967_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.ofNat 4294967295) x4) (UInt256.land (UInt256.ofNat 4294967295) (memLoad ((UInt256.ofNat 0) + x1) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13967) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13996) (uniswapV3PoolCreation_block_13967_fallthrough_stack (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13967_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_13996`. -/
def uniswapV3PoolCreation_block_13996_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 64) + x1) mem) :: (memLoad ((UInt256.ofNat 32) + x1) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 13996. -/
theorem uniswapV3PoolCreation_block_13996 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13996) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_13996_stack (mem := mem) (x1 := x1) (R := R)) mem (M (M aw ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((51) + (memExpansionCost aw ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 13584) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 13584) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13584)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_13996_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13996) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_13996_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_13996 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14017. -/
theorem uniswapV3PoolCreation_block_14017_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (memLoad x0 mem) (UInt256.ofNat 4294967295)) (UInt256.land (UInt256.ofNat 4294967295) x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13471) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14017) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13471) (x0 :: x1 :: x2 :: R) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 13471) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13471) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13471)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14017_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (memLoad x0 mem) (UInt256.ofNat 4294967295)) (UInt256.land (UInt256.ofNat 4294967295) x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13471) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14017) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13471) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14017_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14017. -/
theorem uniswapV3PoolCreation_block_14017_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (memLoad x0 mem) (UInt256.ofNat 4294967295)) (UInt256.land (UInt256.ofNat 4294967295) x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14017) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (x0 :: x1 :: x2 :: R) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 13471) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14036)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14017_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (memLoad x0 mem) (UInt256.ofNat 4294967295)) (UInt256.land (UInt256.ofNat 4294967295) x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14017) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14017_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14036`. -/
def uniswapV3PoolCreation_block_14036_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 64) + x0) mem) :: (memLoad ((UInt256.ofNat 32) + x0) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14036. -/
theorem uniswapV3PoolCreation_block_14036 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_14036_stack (mem := mem) (x0 := x0) (R := R)) mem (M (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((51) + (memExpansionCost aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 13584) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 13584) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13584)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14036_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13584) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14036) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13584) (uniswapV3PoolCreation_block_14036_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14036 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14057_taken`. -/
def uniswapV3PoolCreation_block_14057_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.signextend (UInt256.ofNat 6) (UInt256.sub (memLoad (x0 + (UInt256.ofNat 32)) mem) (memLoad (x1 + (UInt256.ofNat 32)) mem))) :: (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) :: (UInt256.land (UInt256.sub x2 (memLoad x1 mem)) (UInt256.ofNat 4294967295)) :: (UInt256.sub x2 (memLoad x1 mem)) :: (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14057. -/
theorem uniswapV3PoolCreation_block_14057_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13517) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14057) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13517) (uniswapV3PoolCreation_block_14057_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M (M (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 37) (C + ((118) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMload r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 6) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 13517) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13517) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13517)) r37 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14057_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13517) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14057) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13517) (uniswapV3PoolCreation_block_14057_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14057_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14057_fallthrough`. -/
def uniswapV3PoolCreation_block_14057_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.signextend (UInt256.ofNat 6) (UInt256.sub (memLoad (x0 + (UInt256.ofNat 32)) mem) (memLoad (x1 + (UInt256.ofNat 32)) mem))) :: (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) :: (UInt256.land (UInt256.sub x2 (memLoad x1 mem)) (UInt256.ofNat 4294967295)) :: (UInt256.sub x2 (memLoad x1 mem)) :: (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14057. -/
theorem uniswapV3PoolCreation_block_14057_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14057) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14102) (uniswapV3PoolCreation_block_14057_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M (M (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 37) (C + ((118) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x1 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMload r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 6) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 13517) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14102)) r37 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14057_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (memLoad x0 mem) (memLoad x1 mem)) (UInt256.ofNat 4294967295)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14057) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14102) (uniswapV3PoolCreation_block_14057_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14057_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14102. -/
theorem uniswapV3PoolCreation_block_14102 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14102) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14103_taken`. -/
def uniswapV3PoolCreation_block_14103_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.sub (memLoad ((UInt256.ofNat 64) + x5) mem) (memLoad ((UInt256.ofNat 64) + x6) mem))) (UInt256.land (UInt256.ofNat 4294967295) x3)) :: (UInt256.land (UInt256.ofNat 4294967295) x4) :: ((memLoad ((UInt256.ofNat 32) + x6) mem) + (UInt256.mul (UInt256.sdiv x0 x1) x2)) :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14103. -/
theorem uniswapV3PoolCreation_block_14103_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 4294967295) x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13567) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14103) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13567) (uniswapV3PoolCreation_block_14103_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M (M (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x5) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((110) + (memExpansionCost aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x5) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMload r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genMload r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 13567) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13567) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13567)) r33 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14103_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 4294967295) x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13567) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14103) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13567) (uniswapV3PoolCreation_block_14103_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14103_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14103_fallthrough`. -/
def uniswapV3PoolCreation_block_14103_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.sub (memLoad ((UInt256.ofNat 64) + x5) mem) (memLoad ((UInt256.ofNat 64) + x6) mem))) (UInt256.land (UInt256.ofNat 4294967295) x3)) :: (UInt256.land (UInt256.ofNat 4294967295) x4) :: ((memLoad ((UInt256.ofNat 32) + x6) mem) + (UInt256.mul (UInt256.sdiv x0 x1) x2)) :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14103. -/
theorem uniswapV3PoolCreation_block_14103_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 4294967295) x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14103) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14152) (uniswapV3PoolCreation_block_14103_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M (M (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x5) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((110) + (memExpansionCost aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x5) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMload r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genMload r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 13567) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14152)) r33 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14103_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 4294967295) x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14103) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14152) (uniswapV3PoolCreation_block_14103_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14103_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14152. -/
theorem uniswapV3PoolCreation_block_14152 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14152) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14153`. -/
def uniswapV3PoolCreation_block_14153_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad ((UInt256.ofNat 64) + x6) mem) + (UInt256.div x0 x1)) :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14153. -/
theorem uniswapV3PoolCreation_block_14153 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14153) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14170) (uniswapV3PoolCreation_block_14153_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x6 := x6) (R := R)) mem (M aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((41) + (memExpansionCost aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14170)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14153_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14153) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14170) (uniswapV3PoolCreation_block_14153_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14153 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14170`. -/
def uniswapV3PoolCreation_block_14170_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14170. -/
theorem uniswapV3PoolCreation_block_14170 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x9 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14170) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x9 (uniswapV3PoolCreation_block_14170_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 12) (C + ((32))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x9 hvalid) (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14170_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x9 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14170) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x9 (uniswapV3PoolCreation_block_14170_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14170 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14182`. -/
def uniswapV3PoolCreation_block_14182_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.sub x3 ((sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 3)) (⟨0⟩ : UInt256))) (UInt256.ofNat 72057594037927936))) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)) :: (UInt256.ofNat 4294967295) :: ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.sub x3 ((sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 3)) (⟨0⟩ : UInt256))) :: ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 3)) :: (UInt256.ofNat 72057594037927936) :: (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) :: x1 :: x0 :: R)

/-- Final memory for bytecode block summary `uniswapV3PoolCreation_block_14182`. -/
def uniswapV3PoolCreation_block_14182_memory {mem : ByteArray} {x5 : UInt256} {x6 : UInt256} : ByteArray :=
  (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14182. -/
theorem uniswapV3PoolCreation_block_14182 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14182) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14269) (uniswapV3PoolCreation_block_14182_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (uniswapV3PoolCreation_block_14182_memory (mem := mem) (x5 := x5) (x6 := x6)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.sub x3 ((sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMstore r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := RD.genKeccak256 r19 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r31⟩ := RD.sstore r30 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r36⟩ := RD.sload r35 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r42⟩ := RD.sstore r41 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r47⟩ := RD.sload r46 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 216) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.pushConst (UInt256.ofNat 72057594037927936) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14269)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14182_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14182) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14269) (uniswapV3PoolCreation_block_14182_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (uniswapV3PoolCreation_block_14182_memory (mem := mem) (x5 := x5) (x6 := x6)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.sub x3 ((sstoreAccountMap ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.sub x4 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x6.toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) x5)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3PoolCreation_block_14182 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14269`. -/
def uniswapV3PoolCreation_block_14269_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner σ x6 (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 216)))) (UInt256.mul (UInt256.land x4 (UInt256.sub x10 (UInt256.land x4 (UInt256.div (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) x3)))) x3))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) :: (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14269. -/
theorem uniswapV3PoolCreation_block_14269 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14269) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14387) (uniswapV3PoolCreation_block_14269_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x6 (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 216)))) (UInt256.mul (UInt256.land x4 (UInt256.sub x10 (UInt256.land x4 (UInt256.div (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) x3)))) x3))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 6) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.pushConst (UInt256.ofNat 72057594037927935) (width := 7) (op := .PUSH7) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.pushConst (UInt256.ofNat 72057594037927935) (width := 7) (op := .PUSH7) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.push4 (UInt256.ofNat 4294967295) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 216) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r59⟩ := RD.sstore r58 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r60⟩ := RD.sload r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14387)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14269_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14269) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14387) (uniswapV3PoolCreation_block_14269_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x6 (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 216)))) (UInt256.mul (UInt256.land x4 (UInt256.sub x10 (UInt256.land x4 (UInt256.div (UInt256.lor (UInt256.land (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2))) (UInt256.lnot (UInt256.ofNat 72057594037927935))) (UInt256.land (UInt256.ofNat 72057594037927935) (UInt256.signextend (UInt256.ofNat 6) (UInt256.sub x9 (UInt256.signextend (UInt256.ofNat 6) (UInt256.lor (UInt256.land x5 (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)) (UInt256.mul x7 (UInt256.land (UInt256.sub x0 x1) x2)))))))) x3)))) x3))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3PoolCreation_block_14269 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14387`. -/
def uniswapV3PoolCreation_block_14387_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.signextend (UInt256.ofNat 15) (UInt256.div x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14387. -/
theorem uniswapV3PoolCreation_block_14387 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14387) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x2 (uniswapV3PoolCreation_block_14387_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14387_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14387) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 x2 (uniswapV3PoolCreation_block_14387_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14387 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3PoolCreation_block_14393_taken`. -/
def uniswapV3PoolCreation_block_14393_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14393. -/
theorem uniswapV3PoolCreation_block_14393_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 15) x0) (UInt256.ofNat 0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13908) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14393) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13908) (uniswapV3PoolCreation_block_14393_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 13908) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13908) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13908)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3PoolCreation_block_14393_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 15) x0) (UInt256.ofNat 0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode 0).contains (UInt256.ofNat 13908) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14393) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.uniswapV3PoolCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13908) (uniswapV3PoolCreation_block_14393_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3PoolCreation_block_14393_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolCreationBlocks
