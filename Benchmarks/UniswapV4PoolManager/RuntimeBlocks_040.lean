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

/-- Final stack for bytecode block summary `poolManager_block_14631`. -/
def poolManager_block_14631_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14631. -/
theorem poolManager_block_14631 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 17855) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14631) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 17855) (poolManager_block_14631_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14631⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14632⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14633⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 17855) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14634⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 17855), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14637⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17855)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14631_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 17855) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14631) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 17855) (poolManager_block_14631_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14631 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14638`. -/
def poolManager_block_14638_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14638. -/
theorem poolManager_block_14638 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14489) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14638) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14489) (poolManager_block_14638_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14638⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14639⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14640⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14641⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14642⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14643⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14644⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14645⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14646⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 14489) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14647⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14489), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14650⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14489)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14638_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14489) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14638) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14489) (poolManager_block_14638_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14638 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14651_taken`. -/
def poolManager_block_14651_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14651. -/
theorem poolManager_block_14651_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.ofNat 256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14675) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14675) (poolManager_block_14651_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14651⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14652⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14653⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14654⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14655⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14656⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14657⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14658⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14661⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14662⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14675) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14663⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14675), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14666⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14675)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14651_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.ofNat 256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14675) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14675) (poolManager_block_14651_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14651_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14651_fallthrough`. -/
def poolManager_block_14651_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14651. -/
theorem poolManager_block_14651_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.ofNat 256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14667) (poolManager_block_14651_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14651⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14652⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14653⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14654⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14655⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14656⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14657⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14658⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14661⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14662⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14675) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14663⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14675), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14666⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14667)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14651_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.land x6 (UInt256.ofNat 256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14667) (poolManager_block_14651_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14651_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14667`. -/
def poolManager_block_14667_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14667. -/
theorem poolManager_block_14667 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x7 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14667) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x7 (poolManager_block_14667_stack (R := R)) mem aw rdata σ (k + 8) (C + ((22))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14667⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14668⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14669⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14670⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14671⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14672⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14673⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14674⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14667_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x7 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14667) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x7 (poolManager_block_14667_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14667 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14675`. -/
def poolManager_block_14675_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat ee.source.val) :: x3 :: x4 :: x6 :: x0 :: x1 :: x2 :: (UInt256.ofNat 14575) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 14752) :: (memLoad (UInt256.ofNat 64) mem) :: x5 :: (UInt256.ofNat 14631) :: (UInt256.ofNat 14638) :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `poolManager_block_14675`. -/
def poolManager_block_14675_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 48927076799537410738591317824729890221088287177367674182903010818651347484672).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14675. -/
theorem poolManager_block_14675 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14227) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14227) (poolManager_block_14675_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (poolManager_block_14675_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((96) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14675⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14638) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14676⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14638), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap8 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14679⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap10 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14680⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14681⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14682⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14683⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14684⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14685⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 14575) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14686⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14575), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14689⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 14752) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14690⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14752), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14693⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14694⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 14631) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14695⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14631), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14698⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14699⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMload r17 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14701⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap8 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14702⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14703⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14704⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 48927076799537410738591317824729890221088287177367674182903010818651347484672) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14705⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 48927076799537410738591317824729890221088287177367674182903010818651347484672), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14738⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup10 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14740⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14741⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14742⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.caller (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14743⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14744⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup10 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14746⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14747⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 14227) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14748⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14227), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14751⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14227)) r32 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14675_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14227) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14675) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14227) (poolManager_block_14675_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (poolManager_block_14675_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14675 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14752`. -/
def poolManager_block_14752_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.isZero (UInt256.isZero (UInt256.land x1 (UInt256.ofNat 1)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14752. -/
theorem poolManager_block_14752 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 17823) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14752) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 17823) (poolManager_block_14752_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14752⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14753⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14755⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14756⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14757⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14758⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14759⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 17823) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14760⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 17823), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14763⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17823)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14752_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 17823) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14752) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 17823) (poolManager_block_14752_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14752 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14764`. -/
def poolManager_block_14764_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14764. -/
theorem poolManager_block_14764 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x6 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14764) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x6 (poolManager_block_14764_stack (R := R)) mem aw rdata σ (k + 11) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14764⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14765⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14766⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14767⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14768⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14769⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14770⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14771⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14772⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14773⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14774⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14764_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains x6 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14764) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 x6 (poolManager_block_14764_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14764 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14775_taken`. -/
def poolManager_block_14775_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14775. -/
theorem poolManager_block_14775_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14953) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14775) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14953) (poolManager_block_14775_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14775⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14776⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14778⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14779⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14780⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14781⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 14953) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14782⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14953), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14785⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14953)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14775_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14953) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14775) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14953) (poolManager_block_14775_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14775_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14775_fallthrough`. -/
def poolManager_block_14775_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14775. -/
theorem poolManager_block_14775_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14775) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (poolManager_block_14775_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14775⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14776⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14778⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14779⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14780⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14781⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 14953) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14782⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14953), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14785⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14786)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14775_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 128))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14775) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (poolManager_block_14775_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14775_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14786_taken`. -/
def poolManager_block_14786_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14786. -/
theorem poolManager_block_14786_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14786_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14786⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14787⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14790⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14911)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14786_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14786_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14786_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14786_fallthrough`. -/
def poolManager_block_14786_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14786. -/
theorem poolManager_block_14786_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (poolManager_block_14786_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14786⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14787⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14790⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14791)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14786_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14786) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (poolManager_block_14786_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14786_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14791_taken`. -/
def poolManager_block_14791_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14791. -/
theorem poolManager_block_14791_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14941) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14941) (poolManager_block_14791_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14791⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14793⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14794⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14795⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14796⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14941) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14797⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14941), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14800⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14941)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14791_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14941) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14941) (poolManager_block_14791_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14791_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14791_fallthrough`. -/
def poolManager_block_14791_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14791. -/
theorem poolManager_block_14791_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (poolManager_block_14791_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14791⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14793⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14794⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14795⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14796⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14941) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14797⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14941), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14800⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14801)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14791_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14791) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (poolManager_block_14791_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14791_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14801_taken`. -/
def poolManager_block_14801_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14801. -/
theorem poolManager_block_14801_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14801_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14801⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14802⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14805⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14911)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14801_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14801_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14801_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14801_fallthrough`. -/
def poolManager_block_14801_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14801. -/
theorem poolManager_block_14801_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (poolManager_block_14801_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14801⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14802⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14805⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14806)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14801_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14801) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (poolManager_block_14801_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14801_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14806_taken`. -/
def poolManager_block_14806_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14806. -/
theorem poolManager_block_14806_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14929) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14929) (poolManager_block_14806_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1024) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14806⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1024), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14809⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14810⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14811⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14812⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14929) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14813⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14929), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14816⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14929)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14806_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14929) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14929) (poolManager_block_14806_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14806_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14806_fallthrough`. -/
def poolManager_block_14806_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14806. -/
theorem poolManager_block_14806_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (poolManager_block_14806_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1024) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14806⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1024), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14809⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14810⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14811⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14812⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14929) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14813⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14929), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14816⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14817)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14806_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.ofNat 1024))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14806) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (poolManager_block_14806_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14806_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14817_taken`. -/
def poolManager_block_14817_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14817. -/
theorem poolManager_block_14817_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14817_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14817⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14818⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14821⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14911)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14817_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 14911) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14911) (poolManager_block_14817_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14817_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_14817_fallthrough`. -/
def poolManager_block_14817_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14817. -/
theorem poolManager_block_14817_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14822) (poolManager_block_14817_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14817⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14911) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14818⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14911), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨14821⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14822)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_14817_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14817) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 14822) (poolManager_block_14817_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_14817_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end poolManagerBlocks
