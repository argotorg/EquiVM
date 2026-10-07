import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.Attester.Bytecode
import Benchmarks.EAS.Attester.Immutables

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterRuntimeBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.EAS.Attester.Immutables.immutableLayout.sites = [(824, 32, "_eas"), (1719, 32, "_eas"), (1888, 32, "_eas"), (2289, 32, "_eas")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.EAS.Attester.Immutables.immutableLayout.inBounds Benchmarks.EAS.Attester.attesterBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.EAS.Attester.attesterBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords).size = Benchmarks.EAS.Attester.attesterBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: ((x0 + (UInt256.shiftLeft (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 5))) + (UInt256.ofNat 64)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3304. -/
theorem attesterRuntime_block_3304 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((92) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3304⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3305⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3307⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3309⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3310⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3311⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3313⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3314⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3315⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3316⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3317⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3318⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3319⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3320⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3321⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3323⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3324⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3325⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3326⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3327⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3329⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3330⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.shl (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3332⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3333⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3334⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3335⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3336⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3337⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3338⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3340⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3341⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3342⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3344)) r32 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3304_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3304 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3097) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3344⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3345⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3346⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3347⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3348⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3097) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3349⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3352⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3097)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3344_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3097) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3344⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3345⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3346⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3347⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3348⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3097) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3349⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3352⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3353)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3344_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) :: (x4 + (UInt256.ofNat 96)) :: ((UInt256.ofNat 96) + (x4 + (UInt256.shiftLeft (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 5)))) :: ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x6 : UInt256} : ByteArray :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3353. -/
theorem attesterRuntime_block_3353 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) (M (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 51) (C + ((153) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3353⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3386⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3387⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3388⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3389⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3390⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3391⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3392⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3393⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3394⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3395⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3396⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3397⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3398⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3400⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3401⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3402⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMload r17 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3403⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3404⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3406⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3407⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3408⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3409⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3410⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := RD.genMstore r24 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3411⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3412⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMload r26 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3413⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3414⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3415⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3416⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3417⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3418⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := RD.genMstore r32 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3419⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3420⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3421⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3422⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3423⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3425⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3427⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3428⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.shl (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3429⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3430⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3431⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3432⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3433⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3434⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3435⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3436⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3437⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := r49.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3438⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3439⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3441)) r51 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3353_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3353 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3521) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3441⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3442⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3443⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3444⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3445⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3521) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3446⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3521), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3449⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3521)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3521) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3441⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3442⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3443⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3444⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3445⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3521) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3446⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3521), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3449⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3450)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x4 (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)) :: x3 :: (UInt256.ofNat 3499) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} {x9 : UInt256} : ByteArray :=
  (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3450. -/
theorem attesterRuntime_block_3450 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3109) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) (M (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3450⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup11 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3483⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3484⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3485⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3486⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3487⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3488⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3499) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3489⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3499), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3492⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3493⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3494⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 3109) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3495⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3109), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3498⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3109)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3450_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3109) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3450 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3499`. -/
def attesterRuntime_block_3499_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x1) :: x2 :: ((UInt256.ofNat 32) + x3) :: x0 :: ((UInt256.ofNat 32) + x5) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3499. -/
theorem attesterRuntime_block_3499 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3441) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw rdata σ (k + 18) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3499⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3500⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3502⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3503⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3504⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3505⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3506⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3507⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3508⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3509⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3510⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3511⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3512⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3513⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3514⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3516⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 3441) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3517⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3441), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3520⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3441)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3499_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3441) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3499 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3521`. -/
def attesterRuntime_block_3521_stack {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x5) :: ((UInt256.ofNat 32) + x6) :: x7 :: ((UInt256.ofNat 32) + x8) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3521. -/
theorem attesterRuntime_block_3521 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3344) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 22) (C + ((64))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3521⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3522⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3523⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3524⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3525⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3526⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3527⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3528⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3530⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3531⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3532⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3533⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3534⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3535⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3536⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3537⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3538⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3539⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3540⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3542⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3344) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3543⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3344), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3546⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3344)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3521_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3344) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3521 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_taken`. -/
def attesterRuntime_block_3547_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3565) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3547⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3548⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3550⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3552⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3553⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3554⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3555⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3556⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3565) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3557⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3565), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3560⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3565)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3565) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_fallthrough`. -/
def attesterRuntime_block_3547_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3547⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3548⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3550⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3552⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3553⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3554⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3555⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3556⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3565) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3557⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3565), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3560⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3561)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3561. -/
theorem attesterRuntime_block_3561 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3561⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3563⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3564⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_taken`. -/
def attesterRuntime_block_3565_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3588) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3565⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3566⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3567⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3568⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3577⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3578⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3579⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3588) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3580⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3588), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3583⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3588)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3588) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_fallthrough`. -/
def attesterRuntime_block_3565_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3565⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3566⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3567⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3568⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3577⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3578⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3579⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3588) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3580⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3588), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3583⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3584)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3584. -/
theorem attesterRuntime_block_3584 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3584⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3586⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3587⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_taken`. -/
def attesterRuntime_block_3588_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3605) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3588⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3589⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3590⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3591⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3593⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3594⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3595⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sgt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3596⟩ : UInt256), UInt8.ofNat 19, .SGT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3605) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3597⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3605), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3600⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3605)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3605) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_fallthrough`. -/
def attesterRuntime_block_3588_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3588⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3589⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3590⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3591⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3593⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3594⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3595⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sgt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3596⟩ : UInt256), UInt8.ofNat 19, .SGT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3605) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3597⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3605), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3600⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3601)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3601. -/
theorem attesterRuntime_block_3601 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3601⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3603⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3604⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_taken`. -/
def attesterRuntime_block_3605_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3631) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3605⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3606⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3607⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3608⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3617⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3618⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3619⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3631) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3620⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3631), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3623⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3631)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3631) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_fallthrough`. -/
def attesterRuntime_block_3605_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3605⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3606⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3607⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3608⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3617⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3618⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3619⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3631) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3620⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3631), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3623⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3624)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
