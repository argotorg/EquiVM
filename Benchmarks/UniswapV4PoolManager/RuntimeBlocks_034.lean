import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.UniswapV4PoolManager.Bytecode
import Benchmarks.UniswapV4PoolManager.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.UniswapV4PoolManager.immutableLayout.sites = [(13606, 32, "original")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.UniswapV4PoolManager.immutableLayout.inBounds Benchmarks.UniswapV4PoolManager.poolManagerBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.UniswapV4PoolManager.poolManagerBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords).size = Benchmarks.UniswapV4PoolManager.poolManagerBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `poolManager_block_11948`. -/
def poolManager_block_11948_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 11960) :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11948. -/
theorem poolManager_block_11948 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11794) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11948) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11794) (poolManager_block_11948_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11948⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11950⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11951⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11960) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11952⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11960), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11955⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11794) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11956⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11794), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11959⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11794)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_11948_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11794) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11948) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11794) (poolManager_block_11948_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_11948 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_11960_taken`. -/
def poolManager_block_11960_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11960. -/
theorem poolManager_block_11960_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_11960_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11960⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11961⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11962⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11964⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11965⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11986⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11987⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11988⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11989⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11990⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11993⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_11960_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_11960_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_11960_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_11960_fallthrough`. -/
def poolManager_block_11960_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11960. -/
theorem poolManager_block_11960_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (poolManager_block_11960_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11960⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11961⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11962⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11964⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11965⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11986⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11987⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11988⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11989⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11990⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11993⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11994)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_11960_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11960) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (poolManager_block_11960_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_11960_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_11994_taken`. -/
def poolManager_block_11994_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_11994_taken`. -/
def poolManager_block_11994_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11994. -/
theorem poolManager_block_11994_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_11994_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_11994_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((40) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11994⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11995⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11996⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11998⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11999⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12020⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12021⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12022⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12023⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12024⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12027⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_11994_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_11994_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_11994_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_11994_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_11994_fallthrough`. -/
def poolManager_block_11994_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_11994_fallthrough`. -/
def poolManager_block_11994_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11994. -/
theorem poolManager_block_11994_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (poolManager_block_11994_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_11994_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((40) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11994⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11995⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11996⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11998⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨11999⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12020⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12021⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12022⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12023⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12024⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12027⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12028)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_11994_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11994) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (poolManager_block_11994_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_11994_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_11994_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12028_taken`. -/
def poolManager_block_12028_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_12028_taken`. -/
def poolManager_block_12028_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12028. -/
theorem poolManager_block_12028_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12028_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12028_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12028⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12030⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12031⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12032⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 68) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12033⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12035⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12036⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 16777215), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12040⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12041⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12042⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12043⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12044⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12047⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12028_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12028_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12028_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12028_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12028_fallthrough`. -/
def poolManager_block_12028_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_12028_fallthrough`. -/
def poolManager_block_12028_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12028. -/
theorem poolManager_block_12028_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (poolManager_block_12028_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12028_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12028⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12030⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12031⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12032⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 68) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12033⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12035⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12036⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 16777215), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12040⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12041⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12042⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12043⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12044⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12047⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12048)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12028_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12028) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (poolManager_block_12028_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12028_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12028_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12048_taken`. -/
def poolManager_block_12048_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_12048_taken`. -/
def poolManager_block_12048_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12048. -/
theorem poolManager_block_12048_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12048_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12048_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((48) + (memExpansionCost aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12048⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12050⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12051⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12052⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 100) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12053⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12055⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12056⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12057⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12059⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12060⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12061⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12062⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12065⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12048_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12048_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12048_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12048_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12048_fallthrough`. -/
def poolManager_block_12048_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManager_block_12048_fallthrough`. -/
def poolManager_block_12048_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12048. -/
theorem poolManager_block_12048_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (poolManager_block_12048_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12048_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((48) + (memExpansionCost aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12048⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12050⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12051⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12052⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 100) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12053⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12055⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12056⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12057⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12059⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12060⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12061⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12062⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12065⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12066)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12048_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12048) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (poolManager_block_12048_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12048_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12048_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12066_taken`. -/
def poolManager_block_12066_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) :: R)

/-- Final memory for bytecode block summary `poolManager_block_12066_taken`. -/
def poolManager_block_12066_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12066. -/
theorem poolManager_block_12066_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12066_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12066_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((49) + (memExpansionCost aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12066⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12068⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12069⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12070⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 132) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12071⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 132), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12073⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12074⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12075⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12096⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12097⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12098⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12099⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12100⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12103⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12066_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12066_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12066_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12066_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12066_fallthrough`. -/
def poolManager_block_12066_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) :: R)

/-- Final memory for bytecode block summary `poolManager_block_12066_fallthrough`. -/
def poolManager_block_12066_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12066. -/
theorem poolManager_block_12066_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12104) (poolManager_block_12066_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12066_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((49) + (memExpansionCost aw (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12066⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12068⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12069⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12070⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 132) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12071⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 132), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12073⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12074⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12075⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12096⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12097⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12098⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12099⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12100⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12103⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12104)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12066_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12066) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12104) (poolManager_block_12066_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManager_block_12066_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12066_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12104`. -/
def poolManager_block_12104_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `poolManager_block_12104`. -/
def poolManager_block_12104_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem ((UInt256.ofNat 128) + x0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12104. -/
theorem poolManager_block_12104 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12104) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x2 (poolManager_block_12104_stack (R := R)) (poolManager_block_12104_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw ((UInt256.ofNat 128) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((17) + (memExpansionCost aw ((UInt256.ofNat 128) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12104⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12106⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12107⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12108⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12104_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12104) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x2 (poolManager_block_12104_stack (R := R)) (poolManager_block_12104_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12104 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12109_taken`. -/
def poolManager_block_12109_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12109. -/
theorem poolManager_block_12109_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12109_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12109⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12110⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12111⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12112⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12114⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12115⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12116⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12117⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12118⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12121⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12109_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12109_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12109_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12109_fallthrough`. -/
def poolManager_block_12109_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12109. -/
theorem poolManager_block_12109_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (poolManager_block_12109_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12109⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12110⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12111⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12112⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12114⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12115⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12116⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12117⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12118⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12121⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12122)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12109_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (poolManager_block_12109_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12109_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12122_taken`. -/
def poolManager_block_12122_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12122. -/
theorem poolManager_block_12122_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12122_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12122⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12123⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12124⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12125⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12134⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12135⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12136⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12139⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12122_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12122_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12122_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12122_fallthrough`. -/
def poolManager_block_12122_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12122. -/
theorem poolManager_block_12122_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (poolManager_block_12122_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((31))) := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12122⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12123⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12124⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12125⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12134⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12135⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12136⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12139⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12140)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12122_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12122) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (poolManager_block_12122_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12122_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12140_taken`. -/
def poolManager_block_12140_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: (x3 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12140. -/
theorem poolManager_block_12140_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt ((x3 + x2) + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12140_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12140⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12142⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12143⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12144⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12145⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12146⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12147⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12148⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12149⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12150⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12153⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12140_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt ((x3 + x2) + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12140_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12140_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12140_fallthrough`. -/
def poolManager_block_12140_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: (x3 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12140. -/
theorem poolManager_block_12140_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt ((x3 + x2) + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12154) (poolManager_block_12140_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12140⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12142⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12143⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12144⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12145⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12146⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12147⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12148⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12149⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12150⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12153⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12154)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12140_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt ((x3 + x2) + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12140) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12154) (poolManager_block_12140_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12140_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12154`. -/
def poolManager_block_12154_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12154. -/
theorem poolManager_block_12154 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12154) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x0 (poolManager_block_12154_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12154⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12154_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12154) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x0 (poolManager_block_12154_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12154 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_12155_taken`. -/
def poolManager_block_12155_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12155. -/
theorem poolManager_block_12155_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12155) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12155_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12155⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12156⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12157⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12159⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12192⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12193⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12194⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12195⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨12198⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_12155_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12155) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_12155_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_12155_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end poolManagerBlocks
