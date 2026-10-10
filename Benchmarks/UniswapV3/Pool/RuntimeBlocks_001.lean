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

/-- Final stack for bytecode block summary `uniswapV3Pool_block_0_taken`. -/
def uniswapV3Pool_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_0_taken`. -/
def uniswapV3Pool_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem uniswapV3Pool_block_0_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (uniswapV3Pool_block_0_taken_stack (ee := ee) (R := R)) (uniswapV3Pool_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 16) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_0_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (uniswapV3Pool_block_0_taken_stack (ee := ee) (R := R)) (uniswapV3Pool_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_0_fallthrough`. -/
def uniswapV3Pool_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_0_fallthrough`. -/
def uniswapV3Pool_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem uniswapV3Pool_block_0_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 12) (uniswapV3Pool_block_0_fallthrough_stack (ee := ee) (R := R)) (uniswapV3Pool_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 16) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_0_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 12) (uniswapV3Pool_block_0_fallthrough_stack (ee := ee) (R := R)) (uniswapV3Pool_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12. -/
theorem uniswapV3Pool_block_12 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 12) R mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨12⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨14⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨15⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16_taken`. -/
def uniswapV3Pool_block_16_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 16. -/
theorem uniswapV3Pool_block_16_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 430) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 430) (uniswapV3Pool_block_16_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 430) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨22⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 430), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 430)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 430) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 430) (uniswapV3Pool_block_16_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_16_fallthrough`. -/
def uniswapV3Pool_block_16_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 16. -/
theorem uniswapV3Pool_block_16_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) (uniswapV3Pool_block_16_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 430) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨22⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 430), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 26)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_16_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) (uniswapV3Pool_block_16_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_16_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_26_taken`. -/
def uniswapV3Pool_block_26_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem uniswapV3Pool_block_26_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 1892644170) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 238) (uniswapV3Pool_block_26_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨28⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨32⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 1892644170) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨33⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1892644170), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨38⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 238) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨39⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 238)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_26_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 1892644170) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 238) (uniswapV3Pool_block_26_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_26_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_26_fallthrough`. -/
def uniswapV3Pool_block_26_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem uniswapV3Pool_block_26_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 1892644170) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (uniswapV3Pool_block_26_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨28⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨32⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 1892644170) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨33⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1892644170), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨38⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 238) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨39⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 43)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_26_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 1892644170) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (uniswapV3Pool_block_26_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_26_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem uniswapV3Pool_block_43_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3294232917) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 151) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 151) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨43⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3294232917) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨44⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3294232917), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨49⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 151) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨50⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 151), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 151)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_43_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3294232917) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 151) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 151) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_43_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem uniswapV3Pool_block_43_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3294232917) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨43⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3294232917) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨44⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3294232917), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨49⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 151) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨50⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 151), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 54)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_43_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3294232917) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_43_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem uniswapV3Pool_block_54_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3721019203) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 113) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 113) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨54⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3721019203) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨55⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3721019203), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨60⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 113) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨61⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 113), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨64⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 113)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_54_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3721019203) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 113) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 113) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_54_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem uniswapV3Pool_block_54_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3721019203) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨54⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3721019203) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨55⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3721019203), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨60⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 113) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨61⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 113), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨64⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 65)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_54_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 3721019203) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_54_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem uniswapV3Pool_block_65_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3721019203) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2048) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2048) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨65⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3721019203) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨66⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3721019203), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨71⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2048) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨72⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2048), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨75⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2048)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_65_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3721019203) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2048) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2048) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_65_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem uniswapV3Pool_block_65_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3721019203) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨65⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3721019203) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨66⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3721019203), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨71⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2048) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨72⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2048), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨75⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 76)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_65_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3721019203) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_65_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 76. -/
theorem uniswapV3Pool_block_76_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077224857) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2080) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2080) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨76⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4077224857) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨77⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4077224857), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨82⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2080) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨83⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2080), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨86⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2080)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_76_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077224857) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2080) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2080) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_76_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 76. -/
theorem uniswapV3Pool_block_76_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077224857) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨76⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4077224857) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨77⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4077224857), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨82⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2080) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨83⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2080), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨86⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 87)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_76_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077224857) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_76_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 87. -/
theorem uniswapV3Pool_block_87_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077763219) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2088) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2088) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨87⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4077763219) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨88⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4077763219), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨93⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2088) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨94⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2088), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨97⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2088)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_87_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077763219) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2088) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2088) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_87_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 87. -/
theorem uniswapV3Pool_block_87_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077763219) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨87⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4077763219) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨88⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4077763219), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨93⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2088) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨94⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2088), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨97⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 98)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_87_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4077763219) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 87) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_87_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem uniswapV3Pool_block_98_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4130829085) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2218) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2218) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨98⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4130829085) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨99⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4130829085), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨104⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2218) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨105⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2218), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨108⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2218)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_98_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4130829085) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 2218) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 2218) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_98_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem uniswapV3Pool_block_98_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4130829085) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 109) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨98⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4130829085) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨99⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4130829085), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨104⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2218) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨105⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2218), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨108⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 109)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_98_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4130829085) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 98) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 109) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_98_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 109. -/
theorem uniswapV3Pool_block_109 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 430) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 109) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 430) R mem aw rdata σ (k + 2) (C + ((11))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 430) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨109⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 430), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨112⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 430)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_109_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 430) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 109) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 430) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_109 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolBlocks
