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

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3515_taken`. -/
def uniswapV3Pool_block_3515_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 192) + x0) mem) :: (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3515. -/
theorem uniswapV3Pool_block_3515_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3536) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3515) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3536) (uniswapV3Pool_block_3515_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M (M aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((49) + (memExpansionCost aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3517⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3518⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3520⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3521⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3522⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3524⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3525⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3526⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3528⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3529⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3530⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3536) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3531⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3536), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3534⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3536)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3515_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3536) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3515) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3536) (uniswapV3Pool_block_3515_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3515_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3515_fallthrough`. -/
def uniswapV3Pool_block_3515_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 192) + x0) mem) :: (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3515. -/
theorem uniswapV3Pool_block_3515_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3515) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3535) (uniswapV3Pool_block_3515_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M (M aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((49) + (memExpansionCost aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 0) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3517⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3518⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3520⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3521⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3522⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3524⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3525⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3526⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3528⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3529⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3530⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3536) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3531⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3536), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3534⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3535)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3515_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land (UInt256.ofNat 255) (memLoad ((UInt256.ofNat 0) + x3) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3515) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3535) (uniswapV3Pool_block_3515_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3515_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3535. -/
theorem uniswapV3Pool_block_3535 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3535) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) g s0 := by
  let r0 := h
  exact RD.invalid r0 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3535⟩ : UInt256), UInt8.ofNat 254, .INVALID, none, immutableLayout_inBounds, immutableTemplate_size64))

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3536`. -/
def uniswapV3Pool_block_3536_stack {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_3536`. -/
def uniswapV3Pool_block_3536_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) ((UInt256.div x0 x1) + (memLoad (x4 + (UInt256.ofNat 160)) ((UInt256.sub (memLoad (x3 + (UInt256.ofNat 192)) mem) (UInt256.div x0 x1)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)))).toByteArray.write 0 ((UInt256.sub (memLoad (x3 + (UInt256.ofNat 192)) mem) (UInt256.div x0 x1)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3536. -/
theorem uniswapV3Pool_block_3536 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3536) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (uniswapV3Pool_block_3536_stack (x3 := x3) (x4 := x4) (R := R)) (uniswapV3Pool_block_3536_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4)) (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((98) + (memExpansionCost aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3536⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3537⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3539⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3540⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3541⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3542⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3543⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3544⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3545⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3546⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3547⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3548⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3549⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3550⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3551⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3552⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3553⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3555⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3556⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3557⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMload r20 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3558⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3559⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3560⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3561⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3562⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3564⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3566⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3568⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3569⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3570⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3571⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := RD.genMstore r31 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3572⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3573⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3574)) r33 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3536_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3536) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (uniswapV3Pool_block_3536_stack (x3 := x3) (x4 := x4) (R := R)) (uniswapV3Pool_block_3536_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3536 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3574. -/
theorem uniswapV3Pool_block_3574_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (x1 + (UInt256.ofNat 192)) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3637) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem (M aw (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3574⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3575⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3577⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3578⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3579⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3580⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3582⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3584⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3586⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3587⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3588⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3589⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3637) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3590⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3637), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3593⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3637)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3574_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (x1 + (UInt256.ofNat 192)) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3637) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3574_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3574. -/
theorem uniswapV3Pool_block_3574_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (x1 + (UInt256.ofNat 192)) mem))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3594) (x0 :: x1 :: R) mem (M aw (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3574⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3575⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3577⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3578⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3579⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3580⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3582⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3584⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3586⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3587⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3588⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3589⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3637) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3590⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3637), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3593⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3594)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3574_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (x1 + (UInt256.ofNat 192)) mem))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3574) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3594) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3574_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3594`. -/
def uniswapV3Pool_block_3594_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 192) + x1) mem)) :: (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) :: (memLoad ((UInt256.ofNat 192) + x0) mem) :: (UInt256.ofNat 3625) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3594. -/
theorem uniswapV3Pool_block_3594 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_3594_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M (M aw ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 192) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3625) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3594⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3625), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3597⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3598⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3600⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3601⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3602⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3604⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3606⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3607⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3608⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3610⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMload r11 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3611⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3612⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3614⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3616⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3618⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3619⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3620⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 13017) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13017), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3624⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13017)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3594_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_3594_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3594 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3625`. -/
def uniswapV3Pool_block_3625_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_3625`. -/
def uniswapV3Pool_block_3625_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((x0 + (memLoad (x2 + (UInt256.ofNat 128)) mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3625. -/
theorem uniswapV3Pool_block_3625 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3625) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (uniswapV3Pool_block_3625_stack (x1 := x1) (x2 := x2) (R := R)) (uniswapV3Pool_block_3625_memory (mem := mem) (x0 := x0) (x2 := x2)) (M (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((31) + (memExpansionCost aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3625⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3626⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3628⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3629⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3630⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3631⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3632⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3633⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3634⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3635⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3636⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3637)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3625_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3625) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (uniswapV3Pool_block_3625_stack (x1 := x1) (x2 := x2) (R := R)) (uniswapV3Pool_block_3625_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3625 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3637. -/
theorem uniswapV3Pool_block_3637_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 96) + x0) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3934) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3934) (x0 :: x1 :: R) mem (M (M aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 25) (C + ((80) + (memExpansionCost aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3637⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3638⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3639⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3641⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3642⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3643⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3645⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3647⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3649⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3650⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3651⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3652⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3653⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3655⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMload r14 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3656⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3657⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3659⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3663⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3664⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3665⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3666⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3667⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 3934) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3668⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3671⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3934)) r25 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3637_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 96) + x0) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3934) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3934) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3637_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3637. -/
theorem uniswapV3Pool_block_3637_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 96) + x0) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: x1 :: R) mem (M (M aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 25) (C + ((80) + (memExpansionCost aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3637⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3638⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3639⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3641⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3642⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3643⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3645⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3647⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3649⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3650⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3651⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3652⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3653⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3655⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMload r14 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3656⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3657⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3659⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3663⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3664⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3665⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3666⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3667⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 3934) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3668⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3671⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3672)) r25 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3637_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 64) + x1) mem)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((UInt256.ofNat 96) + x0) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3637_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3672. -/
theorem uniswapV3Pool_block_3672_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 64) + x0) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3893) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3893) (x0 :: R) mem (M aw ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3672⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3673⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3675⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3676⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3677⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3893) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3678⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3893), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3681⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3893)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3672_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 64) + x0) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3893) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3893) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3672_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3672. -/
theorem uniswapV3Pool_block_3672_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 64) + x0) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: R) mem (M aw ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw ((UInt256.ofNat 64) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3672⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3673⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3675⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3676⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3677⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3893) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3678⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3893), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3681⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3682)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3672_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 64) + x0) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3672) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3672_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3682. -/
theorem uniswapV3Pool_block_3682_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (memLoad ((UInt256.ofNat 160) + x3) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3775) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: R) mem (M aw ((UInt256.ofNat 160) + x3) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((25) + (memExpansionCost aw ((UInt256.ofNat 160) + x3) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3682⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3683⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3685⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3686⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3775) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3687⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3775), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3690⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3775)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3682_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (memLoad ((UInt256.ofNat 160) + x3) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3775) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3682_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3682. -/
theorem uniswapV3Pool_block_3682_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (memLoad ((UInt256.ofNat 160) + x3) mem) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3691) (x0 :: x1 :: x2 :: x3 :: R) mem (M aw ((UInt256.ofNat 160) + x3) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((25) + (memExpansionCost aw ((UInt256.ofNat 160) + x3) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3682⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3683⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3685⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3686⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3775) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3687⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3775), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3690⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3691)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3682_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (memLoad ((UInt256.ofNat 160) + x3) mem) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3691) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3682_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3691`. -/
def uniswapV3Pool_block_3691_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 96) + x4) mem) :: (memLoad ((UInt256.ofNat 32) + x3) mem) :: (memLoad ((UInt256.ofNat 64) + x4) mem) :: (memLoad ((UInt256.ofNat 32) + x4) mem) :: (UInt256.ofNat 0) :: (memLoad ((UInt256.ofNat 64) + x3) mem) :: (UInt256.ofNat 8) :: (UInt256.ofNat 3741) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3691. -/
theorem uniswapV3Pool_block_3691 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 13193)) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3691) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 13193)) (uniswapV3Pool_block_3691_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M (M (M (M (M aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x4) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((110) + (memExpansionCost aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw ((UInt256.ofNat 64) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + x4) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x4) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3741) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3741), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3694⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3695⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3697⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3698⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3699⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3701⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3702⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3704⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3705⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3706⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3707⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3709⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3710⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3711⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3712⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3714⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMload r17 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3715⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup11 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3716⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3717⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3719⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genMload r21 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3720⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 8) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3721⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 8), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 13193) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3723⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13193), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3726⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.swap7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3727⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3728⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3729⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3730⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3731⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3732⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3733⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.push4 (UInt256.ofNat 4294967295) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3734⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4294967295), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3739⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3740⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r35 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3691_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 13193)) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3691) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 13193)) (uniswapV3Pool_block_3691_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3691 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3741`. -/
def uniswapV3Pool_block_3741_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_3741`. -/
def uniswapV3Pool_block_3741_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x5 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 6) (UInt256.signextend (UInt256.ofNat 6) x1)).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (x5 + (UInt256.ofNat 128)).toNat 32) (x5 + (UInt256.ofNat 96)).toNat 32) (x5 + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3741. -/
theorem uniswapV3Pool_block_3741 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3741) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (uniswapV3Pool_block_3741_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (uniswapV3Pool_block_3741_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5)) (M (M (M aw (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 26) (C + ((80) + (memExpansionCost aw (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3741⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3742⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3744⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3746⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3748⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3749⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3750⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3751⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3753⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3754⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3755⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3756⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3758⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3759⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3760⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3761⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.signextend (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3762⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3763⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3765⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3766⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMstore r20 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3767⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3768⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3770⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3772⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3773⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3774⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3775)) r26 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3741_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3741) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (uniswapV3Pool_block_3741_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (uniswapV3Pool_block_3741_memory (mem := mem) (x0 := x0) (x1 := x1) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3741 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3775_taken`. -/
def uniswapV3Pool_block_3775_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 32) + x0) mem) :: (UInt256.ofNat 3851) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3775. -/
theorem uniswapV3Pool_block_3775_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : x11 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3798) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3798) (uniswapV3Pool_block_3775_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3775⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3776⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3851) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3778⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3851), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3781⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3782⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3784⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3785⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup15 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3786⟩ : UInt256), UInt8.ofNat 142, .DUP15, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3798) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3787⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3798), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3790⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3798)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3775_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : x11 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3798) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3798) (uniswapV3Pool_block_3775_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3775_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3775_fallthrough`. -/
def uniswapV3Pool_block_3775_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 32) + x0) mem) :: (UInt256.ofNat 3851) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3775. -/
theorem uniswapV3Pool_block_3775_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : x11 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3791) (uniswapV3Pool_block_3775_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem (M aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3775⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3776⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3851) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3778⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3851), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3781⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3782⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3784⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3785⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup15 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3786⟩ : UInt256), UInt8.ofNat 142, .DUP15, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3798) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3787⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3798), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3790⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3791)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3775_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : x11 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3775) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3791) (uniswapV3Pool_block_3775_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3775_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3791`. -/
def uniswapV3Pool_block_3791_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3791. -/
theorem uniswapV3Pool_block_3791 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3804) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3791) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3804) (uniswapV3Pool_block_3791_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3791⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3793⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3804) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3794⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3804), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3797⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3804)) r4 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3791_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 3804) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3791) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3804) (uniswapV3Pool_block_3791_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_3791 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_3798`. -/
def uniswapV3Pool_block_3798_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 128) + x4) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3798. -/
theorem uniswapV3Pool_block_3798 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3798) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3804) (uniswapV3Pool_block_3798_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M aw ((UInt256.ofNat 128) + x4) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((13) + (memExpansionCost aw ((UInt256.ofNat 128) + x4) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3798⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3799⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3800⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3802⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨3803⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3804)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_3798_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3798) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 3804) (uniswapV3Pool_block_3798_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_3798 hstack h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolBlocks
