import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV4PoolManager.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 13901. -/
theorem poolManagerCreation_block_13901 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13901) R mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 32754936060235842233766999496646880210696060726502698976450834618736336437248) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `poolManagerCreation_block_13941`. -/
def poolManagerCreation_block_13941_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 13879) :: x3 :: x4 :: x0 :: (UInt256.ofNat 288) :: x6 :: x5 :: (UInt256.ofNat 13903) :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_13941`. -/
def poolManagerCreation_block_13941_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad (x2 + (UInt256.ofNat 128)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 13941. -/
theorem poolManagerCreation_block_13941 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13941) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14063) (poolManagerCreation_block_13941_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (poolManagerCreation_block_13941_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((192) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 13879) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 288) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 13903) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := RD.genMstore r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := RD.genMload r32 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := RD.genMstore r37 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := RD.genMload r42 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := RD.genMstore r47 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := RD.genMload r51 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := RD.genMstore r57 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := RD.genMload r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := RD.genMstore r63 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14063)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_13941_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13941) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14063) (poolManagerCreation_block_13941_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (poolManagerCreation_block_13941_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_13941 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14063`. -/
def poolManagerCreation_block_14063_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14063. -/
theorem poolManagerCreation_block_14063 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14063) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14063_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x0 hvalid) (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14063_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14063) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14063_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14063 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14064`. -/
def poolManagerCreation_block_14064_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x4 :: (x2 + x3) :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_14064`. -/
def poolManagerCreation_block_14064_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32) (x2 + (UInt256.ofNat 256)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14064. -/
theorem poolManagerCreation_block_14064 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12396) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14064) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12396) (poolManagerCreation_block_14064_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (poolManagerCreation_block_14064_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) (M (M (M aw (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((57) + (memExpansionCost aw (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 12396) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12396) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12396)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14064_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12396) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14064) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12396) (poolManagerCreation_block_14064_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (poolManagerCreation_block_14064_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14064 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14088`. -/
def poolManagerCreation_block_14088_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14088. -/
theorem poolManagerCreation_block_14088 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14088) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14088_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14088_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14088) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14088_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14088 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14091`. -/
def poolManagerCreation_block_14091_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: (UInt256.sar (UInt256.ofNat 128) x1) :: x2 :: (UInt256.ofNat 13953) :: x0 :: (UInt256.ofNat 32) :: (UInt256.ofNat 1461501637330902918203684832716283019655932542975) :: x1 :: x2 :: (UInt256.ofNat 12705) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14091. -/
theorem poolManagerCreation_block_14091 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12528) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14091) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12528) (poolManagerCreation_block_14091_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((60) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12705) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 13953) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMload r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.sar (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 12528) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12528) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12528)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14091_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12528) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14091) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12528) (poolManagerCreation_block_14091_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14091 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14138`. -/
def poolManagerCreation_block_14138_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad (x0 + x1) mem) x2) :: (UInt256.signextend (UInt256.ofNat 15) x3) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14138. -/
theorem poolManagerCreation_block_14138 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12528) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14138) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12528) (poolManagerCreation_block_14138_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 12528) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12528) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12528)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14138_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12528) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14138) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12528) (poolManagerCreation_block_14138_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14138 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14151_taken`. -/
def poolManagerCreation_block_14151_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 16777215) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14151. -/
theorem poolManagerCreation_block_14151_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 16777215) x0) (UInt256.ofNat 1000000)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 13984) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14151) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13984) (poolManagerCreation_block_14151_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13984) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 13984) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13984)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14151_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 16777215) x0) (UInt256.ofNat 1000000)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 13984) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14151) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 13984) (poolManagerCreation_block_14151_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14151_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14151_fallthrough`. -/
def poolManagerCreation_block_14151_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 16777215) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14151. -/
theorem poolManagerCreation_block_14151_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 16777215) x0) (UInt256.ofNat 1000000)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14151) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14167) (poolManagerCreation_block_14151_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13984) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14167)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14151_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 16777215) x0) (UInt256.ofNat 1000000)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14151) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14167) (poolManagerCreation_block_14151_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14151_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14167`. -/
def poolManagerCreation_block_14167_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14167. -/
theorem poolManagerCreation_block_14167 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14167) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14167_stack (R := R)) mem aw rdata σ (k + 2) (C + ((10))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r2 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14167_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14167) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14167_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14167 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14169. -/
theorem poolManagerCreation_block_14169 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14169) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 9046485241533758531933624649420484596249631237704994716609821254886193364992) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `poolManagerCreation_block_14212`. -/
def poolManagerCreation_block_14212_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 14152) :: x3 :: (UInt256.ofNat 14199) :: x0 :: (UInt256.ofNat 352) :: x5 :: x4 :: (UInt256.ofNat 13903) :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_14212`. -/
def poolManagerCreation_block_14212_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad (x2 + (UInt256.ofNat 128)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14212. -/
theorem poolManagerCreation_block_14212 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14212) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14336) (poolManagerCreation_block_14212_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (poolManagerCreation_block_14212_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((192) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 13903) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14152) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 352) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 14199) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := RD.genMstore r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := RD.genMload r32 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := RD.genMstore r37 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := RD.genMload r42 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := RD.genMstore r47 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := RD.genMload r51 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := RD.genMstore r57 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := RD.genMload r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := RD.genMstore r63 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14336)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14212_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14212) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14336) (poolManagerCreation_block_14212_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (poolManagerCreation_block_14212_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14212 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14336`. -/
def poolManagerCreation_block_14336_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14336. -/
theorem poolManagerCreation_block_14336 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14336) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14336_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x0 hvalid) (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14336_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14336) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14336_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14336 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14337`. -/
def poolManagerCreation_block_14337_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_14337`. -/
def poolManagerCreation_block_14337_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 96) + x0) ((memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32))).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32))).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32) (x2 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32))).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32))).toByteArray.write 0 ((UInt256.signextend (UInt256.ofNat 2) (memLoad x0 mem)).toByteArray.write 0 mem (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32) (x2 + (UInt256.ofNat 256)).toNat 32) (x2 + (UInt256.ofNat 288)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14337. -/
theorem poolManagerCreation_block_14337 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14337) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14337_stack (x2 := x2) (R := R)) (poolManagerCreation_block_14337_memory (mem := mem) (x0 := x0) (x2 := x2)) (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) rdata σ (k + 37) (C + ((118) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x0) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := RD.genMstore r20 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := RD.genMstore r28 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := RD.genMload r31 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push2 (UInt256.ofNat 288) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := RD.genMstore r35 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r37 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14337_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14337) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_14337_stack (x2 := x2) (R := R)) (poolManagerCreation_block_14337_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14337 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14384`. -/
def poolManagerCreation_block_14384_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x2 :: (x0 + x1) :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_14384`. -/
def poolManagerCreation_block_14384_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem (x0 + (UInt256.ofNat 320)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14384. -/
theorem poolManagerCreation_block_14384 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12396) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14384) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12396) (poolManagerCreation_block_14384_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (poolManagerCreation_block_14384_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x0 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((33) + (memExpansionCost aw (x0 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 320) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 12396) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12396) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12396)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14384_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12396) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14384) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12396) (poolManagerCreation_block_14384_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (poolManagerCreation_block_14384_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14384 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14398_taken`. -/
def poolManagerCreation_block_14398_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.signextend (UInt256.ofNat 15) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14398. -/
theorem poolManagerCreation_block_14398_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.signextend (UInt256.ofNat 15) x0) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12488) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14398) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12488) (poolManagerCreation_block_14398_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 12488) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 12488) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12488)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14398_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.signextend (UInt256.ofNat 15) x0) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 12488) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14398) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12488) (poolManagerCreation_block_14398_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14398_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14398_fallthrough`. -/
def poolManagerCreation_block_14398_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.signextend (UInt256.ofNat 15) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14398. -/
theorem poolManagerCreation_block_14398_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.signextend (UInt256.ofNat 15) x0) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14398) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (poolManagerCreation_block_14398_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 12488) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14411)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14398_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.signextend (UInt256.ofNat 15) x0) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14398) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (poolManagerCreation_block_14398_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14398_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14411`. -/
def poolManagerCreation_block_14411_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14411. -/
theorem poolManagerCreation_block_14411 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14411_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x0 hvalid) (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14411_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_14411_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14411 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14412`. -/
def poolManagerCreation_block_14412_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 32)) :: (UInt256.ofNat 128) :: (UInt256.land (memLoad (x2 + (UInt256.ofNat 128)) ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: (UInt256.ofNat 14354) :: x3 :: (UInt256.ofNat 14401) :: x4 :: x5 :: x0 :: (UInt256.ofNat 416) :: x7 :: x6 :: (UInt256.ofNat 13903) :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_14412`. -/
def poolManagerCreation_block_14412_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.signextend (UInt256.ofNat 2) (memLoad (x2 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32))).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 16777215)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x2 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)).toNat 32) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14412. -/
theorem poolManagerCreation_block_14412 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14412) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14536) (poolManagerCreation_block_14412_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (poolManagerCreation_block_14412_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((192) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((x0 + (UInt256.ofNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14401) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14354) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 13903) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 416) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMstore r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := RD.genMload r26 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := RD.genMstore r29 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := RD.genMload r34 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := RD.genMstore r39 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := RD.genMload r44 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := RD.genMstore r49 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := RD.genMload r53 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := RD.genMstore r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := RD.genMload r61 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14536)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14412_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14412) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14536) (poolManagerCreation_block_14412_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (poolManagerCreation_block_14412_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14412 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_14536`. -/
def poolManagerCreation_block_14536_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `poolManagerCreation_block_14536`. -/
def poolManagerCreation_block_14536_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (x0 + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14536. -/
theorem poolManagerCreation_block_14536 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14536) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x3 (poolManagerCreation_block_14536_stack (R := R)) (poolManagerCreation_block_14536_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x3 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_14536_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x3 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14536) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x3 (poolManagerCreation_block_14536_stack (R := R)) (poolManagerCreation_block_14536_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_14536 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end poolManagerCreationBlocks
