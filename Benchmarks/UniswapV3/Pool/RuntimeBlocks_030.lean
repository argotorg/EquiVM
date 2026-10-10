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

theorem immutableDecode_9149 (immWords : String → UInt256) :
    decode (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) (⟨9149⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "token0", 32)) := by
  exact Layout.decodeSite (pc := (⟨9149⟩ : UInt256)) (words := immWords)
    9150 "token0" [(8315, immWords "factory"), (8829, immWords "factory"), (10457, immWords "factory"), (2258, immWords "token0"), (4853, immWords "token0"), (6740, immWords "token0"), (7822, immWords "token0")] [(15650, immWords "token0"), (4551, immWords "token1"), (6789, immWords "token1"), (7924, immWords "token1"), (9284, immWords "token1"), (10529, immWords "token1"), (15979, immWords "token1"), (3311, immWords "fee"), (6603, immWords "fee"), (6658, immWords "fee"), (10565, immWords "fee"), (3072, immWords "tickSpacing"), (10493, immWords "tickSpacing"), (19402, immWords "tickSpacing"), (19452, immWords "tickSpacing"), (8174, immWords "maxLiquidityPerTick"), (19295, immWords "maxLiquidityPerTick"), (19350, immWords "maxLiquidityPerTick"), (11259, immWords "original")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size]; try native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize]; try native_decide
      · simp [WriteGapsOk]; try native_decide)
    (by simp [WindowDisjointFromWrites]; try native_decide)

theorem immutableDecode_9283 (immWords : String → UInt256) :
    decode (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) (⟨9283⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "token1", 32)) := by
  exact Layout.decodeSite (pc := (⟨9283⟩ : UInt256)) (words := immWords)
    9284 "token1" [(8315, immWords "factory"), (8829, immWords "factory"), (10457, immWords "factory"), (2258, immWords "token0"), (4853, immWords "token0"), (6740, immWords "token0"), (7822, immWords "token0"), (9150, immWords "token0"), (15650, immWords "token0"), (4551, immWords "token1"), (6789, immWords "token1"), (7924, immWords "token1")] [(10529, immWords "token1"), (15979, immWords "token1"), (3311, immWords "fee"), (6603, immWords "fee"), (6658, immWords "fee"), (10565, immWords "fee"), (3072, immWords "tickSpacing"), (10493, immWords "tickSpacing"), (19402, immWords "tickSpacing"), (19452, immWords "tickSpacing"), (8174, immWords "maxLiquidityPerTick"), (19295, immWords "maxLiquidityPerTick"), (19350, immWords "maxLiquidityPerTick"), (11259, immWords "original")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size]; try native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize]; try native_decide
      · simp [WriteGapsOk]; try native_decide)
    (by simp [WindowDisjointFromWrites]; try native_decide)

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9004_taken`. -/
def uniswapV3Pool_block_9004_taken_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9004. -/
theorem uniswapV3Pool_block_9004_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9042) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9004) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9042) (uniswapV3Pool_block_9004_taken_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9004⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9005⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9007⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9008⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9009⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9010⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9011⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9013⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9015⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9017⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9018⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9019⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9021⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9023⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9024⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9025⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9026⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9027⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9028⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9029⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9030⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9031⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9032⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 9042) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9033⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9042), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9036⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9042)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9004_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9042) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9004) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9042) (uniswapV3Pool_block_9004_taken_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9004_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9004_fallthrough`. -/
def uniswapV3Pool_block_9004_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9004. -/
theorem uniswapV3Pool_block_9004_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9004) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9037) (uniswapV3Pool_block_9004_fallthrough_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9004⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9005⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9007⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9008⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9009⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9010⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9011⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9013⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9015⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9017⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9018⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9019⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9021⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9023⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9024⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9025⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9026⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9027⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9028⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9029⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9030⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9031⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.gt (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9032⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 9042) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9033⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9042), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9036⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9037)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9004_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9004) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9037) (uniswapV3Pool_block_9004_fallthrough_stack (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9004_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9037`. -/
def uniswapV3Pool_block_9037_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9037. -/
theorem uniswapV3Pool_block_9037 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9062) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9037) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (uniswapV3Pool_block_9037_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9037⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9062) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9038⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9062), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9041⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9062)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9037_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9062) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9037) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (uniswapV3Pool_block_9037_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9037 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9042`. -/
def uniswapV3Pool_block_9042_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9042. -/
theorem uniswapV3Pool_block_9042 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9042) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (uniswapV3Pool_block_9042_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9042⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9043⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9045⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9046⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9048⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9050⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9051⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9052⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9053⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9055⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9057⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9059⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9060⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9061⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9062)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9042_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9042) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (uniswapV3Pool_block_9042_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9042 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9062_taken`. -/
def uniswapV3Pool_block_9062_taken_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9062. -/
theorem uniswapV3Pool_block_9062_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9191) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (uniswapV3Pool_block_9062_taken_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9062⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9063⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9064⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9065⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9067⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9069⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9071⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9072⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9073⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9074⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9075⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 9191) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9076⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9191), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9079⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9191)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9062_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9191) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (uniswapV3Pool_block_9062_taken_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9062_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9062_fallthrough`. -/
def uniswapV3Pool_block_9062_fallthrough_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9062. -/
theorem uniswapV3Pool_block_9062_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (uniswapV3Pool_block_9062_fallthrough_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9062⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9063⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9064⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9065⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9067⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9069⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9071⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9072⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9073⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9074⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9075⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 9191) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9076⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9191), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9079⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9080)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9062_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9062) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (uniswapV3Pool_block_9062_fallthrough_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9062_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9080. -/
theorem uniswapV3Pool_block_9080_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9109) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (x0 :: x1 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9080⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9082⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9083⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9085⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9087⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9089⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9090⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9091⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9092⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9093⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9094⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9095⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9096⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9097⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 9109) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9098⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9109), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9101⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9109)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9080_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9109) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9080_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9080. -/
theorem uniswapV3Pool_block_9080_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9102) (x0 :: x1 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9080⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9082⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9083⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9085⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9087⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9089⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9090⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9091⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9092⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9093⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9094⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9095⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9096⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9097⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 9109) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9098⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9109), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9101⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9102)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9080_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9080) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9102) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9080_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9102`. -/
def uniswapV3Pool_block_9102_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x1 + (UInt256.lnot (UInt256.ofNat 0))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9102. -/
theorem uniswapV3Pool_block_9102 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9102) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (uniswapV3Pool_block_9102_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((18))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9102⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9104⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9105⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9106⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9107⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9108⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9109)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9102_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9102) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (uniswapV3Pool_block_9102_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9102 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9109`. -/
def uniswapV3Pool_block_9109_stack {immWords : String → UInt256} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x4 :: (immWords "token0") :: (UInt256.ofNat 9191) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9109. -/
theorem uniswapV3Pool_block_9109 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 15238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 15238) (uniswapV3Pool_block_9109_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) x1)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9109⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9110⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9112⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9113⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9114⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9116⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9118⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9120⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9121⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9122⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9123⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9124⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9125⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9127⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9129⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9131⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9132⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9133⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9134⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9135⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9136⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9137⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9138⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9139⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9140⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9141⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9142⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9143⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9144⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 9191) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9145⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9191), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9148⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.pushConst (immWords "token0") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨9149⟩ : UInt256)
    exact immutableDecode_9149 immWords) (by evm_ov)
  have r33 := r32.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9182⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9183⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9184⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9185⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9186⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 15238) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9187⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9190⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15238)) r39 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9109_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 15238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9109) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 15238) (uniswapV3Pool_block_9109_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) x1)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9109 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9191. -/
theorem uniswapV3Pool_block_9191_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9325) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9325) (x0 :: R) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9191⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9192⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9194⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9196⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9198⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9199⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9200⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9201⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9202⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9325) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9325), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9325)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9191_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9325) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9325) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9191_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9191. -/
theorem uniswapV3Pool_block_9191_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9191⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9192⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9194⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9196⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9198⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9199⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9200⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9201⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9202⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9325) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9325), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9207)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9191_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9191) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9191_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9207. -/
theorem uniswapV3Pool_block_9207_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9240) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (x0 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9207⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9209⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9210⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9212⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9214⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9216⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9217⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9218⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9219⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9220⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9221⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9223⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9225⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9226⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9227⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9228⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9229⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9230⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9231⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 9240) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9232⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9240), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jumpiT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9235⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9240)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9207_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 9240) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9207_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9207. -/
theorem uniswapV3Pool_block_9207_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9236) (x0 :: R) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9207⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9209⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9210⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9212⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9214⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9216⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9217⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9218⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9219⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9220⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9221⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9223⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9225⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9226⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9227⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9228⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9229⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.eq (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9230⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.iszero (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9231⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 9240) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9232⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9240), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jumpiNT (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9235⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9236)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9207_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) x0))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9236) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9207_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9236`. -/
def uniswapV3Pool_block_9236_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.lnot (UInt256.ofNat 0)) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9236. -/
theorem uniswapV3Pool_block_9236 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9236) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (uniswapV3Pool_block_9236_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 3) (C + ((9))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9236⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9238⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9239⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9240)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9236_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9236) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (uniswapV3Pool_block_9236_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9236 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9240`. -/
def uniswapV3Pool_block_9240_stack {immWords : String → UInt256} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x4 :: (immWords "token1") :: (UInt256.ofNat 9325) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9240. -/
theorem uniswapV3Pool_block_9240 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 15238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 15238) (uniswapV3Pool_block_9240_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) (UInt256.mul (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) x0)) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9240⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9241⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9243⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9244⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9245⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9247⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9249⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9251⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9252⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9253⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9255⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9257⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9258⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9259⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.div (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9260⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9261⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9262⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9263⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9264⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9265⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9266⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9267⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.mul (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9268⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9269⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9270⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9271⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9272⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9273⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9274⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9275⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9276⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9277⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sstore r32 hperm (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9278⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 9325) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9279⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9325), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9282⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.pushConst (immWords "token1") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨9283⟩ : UInt256)
    exact immutableDecode_9283 immWords) (by evm_ov)
  have r37 := r36.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9316⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.dup8 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9317⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9318⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.dup5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9319⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9320⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.push2 (UInt256.ofNat 15238) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9321⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9324⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15238)) r43 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9240_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 15238) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9240) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 15238) (uniswapV3Pool_block_9240_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) (UInt256.mul (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) x0)) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9240 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9325`. -/
def uniswapV3Pool_block_9325_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x5 :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `uniswapV3Pool_block_9325`. -/
def uniswapV3Pool_block_9325_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9325. -/
theorem uniswapV3Pool_block_9325 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9325) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9434) (uniswapV3Pool_block_9325_stack (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (R := R)) (uniswapV3Pool_block_9325_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)) ((UInt256.ofNat 64) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32))))) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0) (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240)) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9325⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9326⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9328⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9329⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9330⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9332⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9334⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9336⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9337⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9338⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup6 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9339⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9340⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9341⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9342⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9343⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9344⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9345⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9347⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9348⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9349⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9350⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genMload r21 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9351⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9352⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9354⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9356⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9358⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9359⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.dup9 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9360⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9361⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9362⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.caller (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9363⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9364⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.pushConst (UInt256.ofNat 40445498149136802562839593865433917484469540145091303255853345906055439757649) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9365⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 40445498149136802562839593865433917484469540145091303255853345906055439757649), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.swap3 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9398⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9399⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.dup2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9400⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9401⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.sub (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9402⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9403⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9404⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.add (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9405⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9406⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := RD.genLog3 r42 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9407⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9408⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9410⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r46⟩ := RD.sload r45 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9411⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 255) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9412⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 240) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9414⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 240), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9416⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := r49.not (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9417⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := r50.and (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9418⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9419⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 240) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9421⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 240), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r54 := r53.shl (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9423⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r55 := r54.or (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9424⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r56 := r55.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9425⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r57⟩ := RD.sstore r56 hperm (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9426⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r58 := r57.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9427⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r59 := r58.swap5 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9428⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r60 := r59.swap1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9429⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r61 := r60.swap4 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9430⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r62 := r61.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9431⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r63 := r62.swap2 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9432⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r64 := r63.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9433⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9434)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9325_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9325) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9434) (uniswapV3Pool_block_9325_stack (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (R := R)) (uniswapV3Pool_block_9325_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0) (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240)) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := uniswapV3Pool_block_9325 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9434`. -/
def uniswapV3Pool_block_9434_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 9434. -/
theorem uniswapV3Pool_block_9434 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9434) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x1 (uniswapV3Pool_block_9434_stack (R := R)) mem aw rdata σ (k + 2) (C + ((10))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9434⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9435⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r2 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9434_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9434) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 x1 (uniswapV3Pool_block_9434_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9434 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9436`. -/
def uniswapV3Pool_block_9436_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 9447) :: (UInt256.ofNat 96) :: (UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9436. -/
theorem uniswapV3Pool_block_9436 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11248) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9436) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11248) (uniswapV3Pool_block_9436_stack (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9436⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9437⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9439⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 9447) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9440⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9447), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11248) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9443⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11248), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9446⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11248)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9436_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11248) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9436) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11248) (uniswapV3Pool_block_9436_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9436 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `uniswapV3Pool_block_9447`. -/
def uniswapV3Pool_block_9447_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 9458) :: (UInt256.ofNat 9566) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9447. -/
theorem uniswapV3Pool_block_9447 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9447) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11303) (uniswapV3Pool_block_9447_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9447⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9566) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9448⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9566), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 9458) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9451⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9458), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11303) (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9454⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.UniswapV3.Pool.immutableLayout, Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode, immWords, (⟨9457⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11303)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem uniswapV3Pool_block_9447_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) 0).contains (UInt256.ofNat 11303) = true)
    (h : RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 9447) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV3.Pool.immutableLayout.runtime Benchmarks.UniswapV3.Pool.uniswapV3PoolBytecode immWords) ee g s0 (UInt256.ofNat 11303) (uniswapV3Pool_block_9447_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (uniswapV3Pool_block_9447 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end uniswapV3PoolBlocks
