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

/-- Automatically generated RD summary for bytecode block at pc 18074. -/
theorem uniswapV3Pool_block_18074 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18114) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18074) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18114) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18074⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18114) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18075⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18114), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18078⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18114)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18074_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18114) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18074) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18114) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18074 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18079`. -/
def uniswapV3Pool_block_18079_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96)) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.sub x3 x4)) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x2) :: (UInt256.ofNat 18114) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18079. -/
theorem uniswapV3Pool_block_18079 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16809) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18079) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (uniswapV3Pool_block_18079_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 23) (C + ((72))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18079⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18114) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18080⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18114), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18083⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18084⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18086⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18088⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18090⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18091⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18092⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18093⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18094⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18095⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18096⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18098⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18100⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18102⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18103⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18104⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18105⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18107⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18109⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 16809) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18110⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16809), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18113⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16809)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18079_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16809) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18079) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (uniswapV3Pool_block_18079_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18079 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18114`. -/
def uniswapV3Pool_block_18114_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18114. -/
theorem uniswapV3Pool_block_18114 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18114) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18117) (uniswapV3Pool_block_18114_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 3) (C + ((6))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18114⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18115⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18116⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18117)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18114_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18114) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18117) (uniswapV3Pool_block_18114_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18114 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18117`. -/
def uniswapV3Pool_block_18117_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18117. -/
theorem uniswapV3Pool_block_18117 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18117) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x5 (uniswapV3Pool_block_18117_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18117⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18118⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18119⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18120⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18121⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18122⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18123⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18124⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18117_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18117) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x5 (uniswapV3Pool_block_18117_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18117 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18125_taken`. -/
def uniswapV3Pool_block_18125_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18125. -/
theorem uniswapV3Pool_block_18125_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18157) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18125) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (uniswapV3Pool_block_18125_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 20) (C + ((65))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18125⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18126⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18128⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18129⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18131⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18133⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18135⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18136⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18137⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18138⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18139⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18141⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18143⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18145⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18146⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18147⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18148⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18149⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 18157) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18150⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18157), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18153⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18157)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18125_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18157) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18125) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (uniswapV3Pool_block_18125_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18125_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18125_fallthrough`. -/
def uniswapV3Pool_block_18125_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18125. -/
theorem uniswapV3Pool_block_18125_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18125) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18154) (uniswapV3Pool_block_18125_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 20) (C + ((65))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18125⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18126⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18128⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18129⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18131⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18133⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18135⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18136⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18137⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18138⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18139⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18141⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18143⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18145⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18146⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18147⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18148⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18149⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 18157) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18150⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18157), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18153⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18154)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18125_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x3) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18125) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18154) (uniswapV3Pool_block_18125_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18125_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18154`. -/
def uniswapV3Pool_block_18154_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x4 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18154. -/
theorem uniswapV3Pool_block_18154 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18154) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (uniswapV3Pool_block_18154_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 3) (C + ((9))) := by
  let r0 := h
  have r1 := r0.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18154⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18155⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18156⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18157)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18154_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18154) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (uniswapV3Pool_block_18154_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18154 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18157_taken`. -/
def uniswapV3Pool_block_18157_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.sub x3 x4)) :: (UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 96)) (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880)) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18157. -/
theorem uniswapV3Pool_block_18157_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18217) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (uniswapV3Pool_block_18157_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 22) (C + ((71))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18157⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) (width := 28) (op := .PUSH28) (by decide) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18158⟩ : UInt256), UInt8.ofNat 123, .Push .PUSH28, some ((UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880), 28), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18187⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18189⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18190⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18191⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18192⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18193⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18195⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18197⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18199⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18200⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18201⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18202⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18203⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18204⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18205⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18206⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18207⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18208⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 18217) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18209⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18217), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18212⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18217)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18157_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18217) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (uniswapV3Pool_block_18157_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18157_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18157_fallthrough`. -/
def uniswapV3Pool_block_18157_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.sub x3 x4)) :: (UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 96)) (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880)) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18157. -/
theorem uniswapV3Pool_block_18157_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18213) (uniswapV3Pool_block_18157_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 22) (C + ((71))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18157⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) (width := 28) (op := .PUSH28) (by decide) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18158⟩ : UInt256), UInt8.ofNat 123, .Push .PUSH28, some ((UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880), 28), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18187⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18189⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18190⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18191⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18192⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18193⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18195⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18197⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18199⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18200⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18201⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18202⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18203⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18204⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18205⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18206⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18207⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18208⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 18217) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18209⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18217), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18212⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18213)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18157_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18157) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18213) (uniswapV3Pool_block_18157_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18157_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 18213. -/
theorem uniswapV3Pool_block_18213 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18213) R mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18213⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18215⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18216⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 18217. -/
theorem uniswapV3Pool_block_18217_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x3 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18265) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18265) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18217⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18218⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18265) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18219⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18265), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18222⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18265)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18217_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x3 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18265) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18265) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18217_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 18217. -/
theorem uniswapV3Pool_block_18217_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x3 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18223) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18217⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18218⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18265) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18219⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18265), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18222⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18223)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18217_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : x3 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18217) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18223) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18217_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18223`. -/
def uniswapV3Pool_block_18223_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5) :: x0 :: x1 :: (UInt256.ofNat 18252) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x6) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18223. -/
theorem uniswapV3Pool_block_18223 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18223) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_18223_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 19) (C + ((62))) := by
  let r0 := h
  have r1 := r0.dup7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18223⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18224⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18226⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18228⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18230⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18231⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18232⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 18252) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18233⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18252), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18236⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18237⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18238⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18239⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18241⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18243⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18245⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18246⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18247⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 13017) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18248⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13017), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18251⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13017)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18223_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 13017) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18223) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 13017) (uniswapV3Pool_block_18223_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18223 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 18252. -/
theorem uniswapV3Pool_block_18252_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18259) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18252) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18259) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18252⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18253⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18259) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18254⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18259), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18257⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18259)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18252_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18259) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18252) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18259) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18252_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 18252. -/
theorem uniswapV3Pool_block_18252_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18252) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18258) (x0 :: x1 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18252⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18253⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18259) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18254⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18259), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18257⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18258)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18252_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18252) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18258) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18252_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 18258. -/
theorem uniswapV3Pool_block_18258 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18258) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) g s0 := by
  let r0 := h
  exact RD.invalid r0 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18258⟩ : UInt256), UInt8.ofNat 254, .INVALID, none, immutableLayout_inBounds, immutableTemplate_size64))

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18259`. -/
def uniswapV3Pool_block_18259_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18259. -/
theorem uniswapV3Pool_block_18259 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18259) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18303) (uniswapV3Pool_block_18259_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18259⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18260⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18303) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18261⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18264⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18303)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18259_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 18303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18259) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18303) (uniswapV3Pool_block_18259_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18259 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18265`. -/
def uniswapV3Pool_block_18265_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5) :: x0 :: x1 :: (UInt256.ofNat 18288) :: (UInt256.ofNat 18303) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18265. -/
theorem uniswapV3Pool_block_18265 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16809) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18265) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (uniswapV3Pool_block_18265_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 14) (C + ((45))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18265⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18303) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18266⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18288) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18269⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18288), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18272⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18273⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup10 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18274⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18275⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18277⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18279⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18281⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18282⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18283⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 16809) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18284⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16809), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18287⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16809)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18265_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 16809) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18265) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 16809) (uniswapV3Pool_block_18265_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18265 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18288`. -/
def uniswapV3Pool_block_18288_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x8) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18288. -/
theorem uniswapV3Pool_block_18288 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19703) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18288) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19703) (uniswapV3Pool_block_18288_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18288⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18289⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18290⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18292⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18294⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18296⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18297⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18298⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 19703) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18299⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 19703), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18302⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19703)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18288_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 19703) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18288) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 19703) (uniswapV3Pool_block_18288_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18288 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_18303`. -/
def uniswapV3Pool_block_18303_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18303. -/
theorem uniswapV3Pool_block_18303 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18303) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x8 (uniswapV3Pool_block_18303_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18303⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18304⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap7 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18305⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18306⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18307⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18308⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18309⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18310⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18311⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18312⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨18313⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_18303_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 18303) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x8 (uniswapV3Pool_block_18303_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_18303 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolBlocks
