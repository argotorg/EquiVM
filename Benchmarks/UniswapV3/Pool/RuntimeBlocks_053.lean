import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.UniswapV3.Pool.Bytecode
import Benchmarks.UniswapV3.Pool.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace uniswapV3PoolBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.UniswapV3.Pool.immutableLayout.sites = [(8315, 32, "factory"), (8829, 32, "factory"), (10457, 32, "factory"), (2258, 32, "token0"), (4853, 32, "token0"), (6740, 32, "token0"), (7822, 32, "token0"), (9150, 32, "token0"), (15650, 32, "token0"), (4551, 32, "token1"), (6789, 32, "token1"), (7924, 32, "token1"), (9284, 32, "token1"), (10529, 32, "token1"), (15979, 32, "token1"), (3311, 32, "fee"), (6603, 32, "fee"), (6658, 32, "fee"), (10565, 32, "fee"), (3072, 32, "tickSpacing"), (10493, 32, "tickSpacing"), (19402, 32, "tickSpacing"), (19452, 32, "tickSpacing"), (8174, 32, "maxLiquidityPerTick"), (19295, 32, "maxLiquidityPerTick"), (19350, 32, "maxLiquidityPerTick"), (11259, 32, "original")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.UniswapV3.Pool.immutableLayout.inBounds Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords).size = Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16483`. -/
def uniswapV3Pool_block_16483_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 64) + x6) mem) :: (UInt256.ofNat 16496) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16483. -/
theorem uniswapV3Pool_block_16483 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16483) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16483_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16483⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 16496) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16484⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16496), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16487⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16490⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16491⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11629) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16492⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11629), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16495⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11629)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16483_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16483) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16483_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16483 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16496`. -/
def uniswapV3Pool_block_16496_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 96) + x7) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16496. -/
theorem uniswapV3Pool_block_16496 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19588) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16496) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19588) (uniswapV3Pool_block_16496_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M aw ((UInt256.ofNat 96) + x7) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw ((UInt256.ofNat 96) + x7) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16496⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16497⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16498⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16500⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16501⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19588) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16502⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 19588), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16505⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19588)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16496_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19588) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16496) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19588) (uniswapV3Pool_block_16496_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16496 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16506`. -/
def uniswapV3Pool_block_16506_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16506. -/
theorem uniswapV3Pool_block_16506 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16506) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16506_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16506⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16507⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16508⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 16801) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16509⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16801), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16512⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16801)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16506_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16506) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16506_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16506 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 16513. -/
theorem uniswapV3Pool_block_16513_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 32) + x0) mem)) (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 64) + x4) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16759) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16513) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem (M (M aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((60) + (memExpansionCost aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16513⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16514⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16517⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16518⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16519⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16521⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16522⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16523⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16525⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16526⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16527⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16529⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.slt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16530⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16531⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 16759) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16532⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16759), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16535⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16759)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16513_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 32) + x0) mem)) (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 64) + x4) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16759) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16513) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16513_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 16513. -/
theorem uniswapV3Pool_block_16513_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 32) + x0) mem)) (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 64) + x4) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16513) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16536) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem (M (M aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((60) + (memExpansionCost aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16513⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16514⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16517⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16518⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16519⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16521⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16522⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16523⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16525⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16526⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16527⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16529⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.slt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16530⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16531⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 16759) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16532⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16759), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16535⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16536)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16513_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 32) + x0) mem)) (UInt256.signextend (UInt256.ofNat 2) (memLoad ((UInt256.ofNat 64) + x4) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16513) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16536) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16513_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16536`. -/
def uniswapV3Pool_block_16536_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 16567) :: (memLoad (x0 + (UInt256.ofNat 64)) mem) :: (UInt256.ofNat 16595) :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16536. -/
theorem uniswapV3Pool_block_16536 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16536) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11303) (uniswapV3Pool_block_16536_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M aw (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16536⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16538⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16539⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16541⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16542⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16543⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16544⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16546⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16548⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16550⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16551⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16552⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16553⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16554⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16555⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 16595) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16556⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16595), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16559⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 16567) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16560⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16567), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 11303) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16563⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16566⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11303)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16536_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16536) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11303) (uniswapV3Pool_block_16536_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_16536 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16567`. -/
def uniswapV3Pool_block_16567_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x4 + (UInt256.ofNat 128)) mem) :: (memLoad (x4 + (UInt256.ofNat 96)) mem) :: x3 :: (memLoad (x4 + (UInt256.ofNat 32)) mem) :: x0 :: x1 :: (UInt256.ofNat 8) :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16567. -/
theorem uniswapV3Pool_block_16567 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 14801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16567) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 14801) (uniswapV3Pool_block_16567_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M (M (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((69) + (memExpansionCost aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16567⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16568⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16570⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16571⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16572⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16573⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16575⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16576⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16577⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16578⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16580⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16581⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMload r12 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16582⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 8) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16583⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 8), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16585⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16586⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16587⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16588⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16589⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16590⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 14801) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16591⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14801), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16594⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14801)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16567_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 14801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16567) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 14801) (uniswapV3Pool_block_16567_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16567 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16595`. -/
def uniswapV3Pool_block_16595_stack {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x7 + (UInt256.ofNat 64)) mem) :: (UInt256.ofNat 16665) :: (memLoad x3 mem) :: (UInt256.ofNat 16675) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16595. -/
theorem uniswapV3Pool_block_16595 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16595) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16595_stack (mem := mem) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x3 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0) (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 65535) x1) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 184))) (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 65535) x0) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 200))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16595⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16596⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16598⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16599⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 65535) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16600⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 65535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 200) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16603⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 200), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16605⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16606⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16607⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16608⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 200) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16610⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 200), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16612⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 65535) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16613⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 65535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16616⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16617⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16618⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.mul (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16619⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16620⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 65535) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 65535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 184) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16624⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16626⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16627⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16628⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16629⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 184) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16631⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16633⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16634⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16635⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16636⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16637⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16638⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16639⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16640⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.mul (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16641⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16642⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16643⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r37⟩ := RD.sstore r36 hperm (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16644⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16645⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := RD.genMload r38 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16646⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16647⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16649⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16650⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := RD.genMload r42 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16651⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 16675) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16652⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16675), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16655⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16656⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push2 (UInt256.ofNat 16665) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16657⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16665), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16660⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 11629) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16661⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11629), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := r49.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16664⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11629)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16595_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16595) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16595_stack (mem := mem) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0) (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 65535) x1) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 184))) (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 65535) x0) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 200))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_16595 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16665`. -/
def uniswapV3Pool_block_16665_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 96) + x8) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16665. -/
theorem uniswapV3Pool_block_16665 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19588) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16665) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19588) (uniswapV3Pool_block_16665_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem (M aw ((UInt256.ofNat 96) + x8) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw ((UInt256.ofNat 96) + x8) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16665⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16666⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16667⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16669⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16670⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19588) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16671⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 19588), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16674⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19588)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16665_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19588) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16665) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19588) (uniswapV3Pool_block_16665_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16665 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16675`. -/
def uniswapV3Pool_block_16675_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 32) + x6) mem) :: (UInt256.ofNat 16693) :: (UInt256.ofNat 16705) :: x1 :: x2 :: x3 :: x0 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16675. -/
theorem uniswapV3Pool_block_16675 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16675_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (R := R)) mem (M aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((35) + (memExpansionCost aw ((UInt256.ofNat 32) + x6) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16675⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16676⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16677⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 16705) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16678⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16705), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 16693) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16681⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16693), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16684⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16685⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16687⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16688⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 11629) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16689⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11629), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16692⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11629)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16675_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16675_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16675 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16693`. -/
def uniswapV3Pool_block_16693_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x7 + (UInt256.ofNat 96)) mem) :: (memLoad x3 mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16693. -/
theorem uniswapV3Pool_block_16693 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19656) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16693) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19656) (uniswapV3Pool_block_16693_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x3 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16693⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16694⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16695⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16696⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16698⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16699⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16700⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 19656) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16701⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 19656), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16704⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19656)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16693_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19656) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16693) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19656) (uniswapV3Pool_block_16693_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16693 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16705`. -/
def uniswapV3Pool_block_16705_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 96) + x6) mem) :: x1 :: (UInt256.ofNat 16721) :: x1 :: x2 :: x0 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16705. -/
theorem uniswapV3Pool_block_16705 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13807) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16705) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13807) (uniswapV3Pool_block_16705_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M aw ((UInt256.ofNat 96) + x6) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((35) + (memExpansionCost aw ((UInt256.ofNat 96) + x6) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16705⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16706⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16707⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 16721) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16708⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16721), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16711⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16712⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16713⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16715⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16716⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 13807) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16717⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13807), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16720⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13807)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16705_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13807) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16705) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13807) (uniswapV3Pool_block_16705_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16705 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16721`. -/
def uniswapV3Pool_block_16721_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 16721. -/
theorem uniswapV3Pool_block_16721 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16721) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16721_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16721⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16722⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16724⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16725⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16726⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16728⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16730⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16732⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16733⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16734⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16735⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16736⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16738⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16740⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16742⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16743⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16744⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16745⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16746⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16747⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16748⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16749⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16750⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16751⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16752⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16753⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16754⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 16801) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16755⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16801), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16758⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16801)) r29 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16721_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16801) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16721) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16721_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_16721 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16759`. -/
def uniswapV3Pool_block_16759_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 32) + x4) mem) :: (UInt256.ofNat 16775) :: (UInt256.ofNat 16798) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16759. -/
theorem uniswapV3Pool_block_16759 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16759_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M aw ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16759⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 16798) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16760⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16798), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 16775) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16763⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16775), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16766⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16767⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16769⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16770⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11629) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16771⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11629), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16774⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11629)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16759_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16759_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16759 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16775`. -/
def uniswapV3Pool_block_16775_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 64) + x6) mem) :: (UInt256.ofNat 16788) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16775. -/
theorem uniswapV3Pool_block_16775 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16775_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem (M aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw ((UInt256.ofNat 64) + x6) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16775⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 16788) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16776⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16788), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16779⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16780⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16782⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16783⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11629) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16784⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11629), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16787⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11629)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16775_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11629) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11629) (uniswapV3Pool_block_16775_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16775 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16788`. -/
def uniswapV3Pool_block_16788_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 96) + x7) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16788. -/
theorem uniswapV3Pool_block_16788 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19656) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16788) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19656) (uniswapV3Pool_block_16788_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M aw ((UInt256.ofNat 96) + x7) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw ((UInt256.ofNat 96) + x7) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16788⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16789⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16790⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16792⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16793⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19656) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16794⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 19656), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16797⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19656)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16788_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19656) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16788) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19656) (uniswapV3Pool_block_16788_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16788 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16798`. -/
def uniswapV3Pool_block_16798_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16798. -/
theorem uniswapV3Pool_block_16798 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16798) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16798_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((6))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16798⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16799⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16800⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16801)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16798_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16798) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (uniswapV3Pool_block_16798_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16798 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16801`. -/
def uniswapV3Pool_block_16801_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16801. -/
theorem uniswapV3Pool_block_16801 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x5 (uniswapV3Pool_block_16801_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16801⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16802⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16803⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16804⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16805⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16806⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16807⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16808⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16801_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16801) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x5 (uniswapV3Pool_block_16801_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16801 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16809`. -/
def uniswapV3Pool_block_16809_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: (UInt256.ofNat 16822) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16809. -/
theorem uniswapV3Pool_block_16809 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_16809_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16809⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16810⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 16822) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16812⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16822), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16815⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16816⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16817⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13017) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16818⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13017), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16821⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13017)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16809_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_16809_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16809 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16822_taken`. -/
def uniswapV3Pool_block_16822_taken_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.ofNat 0) :: x0 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 16822. -/
theorem uniswapV3Pool_block_16822_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16834) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16822) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16834) (uniswapV3Pool_block_16822_taken_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16822⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16823⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16824⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16825⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16827⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16828⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 16834) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16829⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16834), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16832⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16834)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16822_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16834) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16822) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16834) (uniswapV3Pool_block_16822_taken_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16822_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolBlocks
