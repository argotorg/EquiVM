import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

/-- The shared prefix of block 18793 retains memory expansion cost through SLOAD. -/
theorem poolSwapProtocolCostBlock {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 22261) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 18793) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ C+Cₘ (poolSwapResultZeroAW aw x4 x1) ≤ C'+Cₘ aw ∧ RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (if (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32))))) = UInt256.ofNat 0 then UInt256.ofNat 18833 else UInt256.ofNat 22261) (poolManager_block_18793_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (poolManager_block_18793_taken_memory (mem := mem) (x4 := x4)) (M (M (M (M aw x4 (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18793⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18794⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18795⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18796⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18797⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18799⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18800⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap3 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18801⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18802⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18803⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18804⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18805⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18807⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18808⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18809⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18810⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup8 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18811⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18812⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18813⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18814⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18815⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, hcost, r22⟩ := RD.sloadMono r21 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18816⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18817⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18818⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18820⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18821⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMload r26 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18822⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.iszero (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18823⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.swap6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18824⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18825⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.iszero (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18826⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18827⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.eq (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18828⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 22261) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨18829⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 22261), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  by_cases hz : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32))))) = UInt256.ofNat 0
  · rw [if_pos hz]
    have r35 := r34.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨18832⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hz (by evm_ov)
    have rFinal := RD.normalizePC (pc' := UInt256.ofNat 18833) r35 (by native_decide)
    refine ⟨_, _, by omega, ?_, rFinal⟩
    dsimp only [poolSwapResultZeroAW, memExpansionCost] at hcost ⊢
    omega
  · rw [if_neg hz]
    have r35 := r34.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨18832⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hz hvalid (by evm_ov)
    have rFinal := RD.normalizePC (pc' := UInt256.ofNat 22261) r35 (by native_decide)
    refine ⟨_, _, by omega, ?_, rFinal⟩
    dsimp only [poolSwapResultZeroAW, memExpansionCost] at hcost ⊢
    omega

end Benchmarks.UniswapV4PoolManager
