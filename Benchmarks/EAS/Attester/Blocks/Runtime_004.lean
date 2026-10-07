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

theorem immutableDecode_823 (immWords : String → UInt256) :
    decode (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) (⟨823⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "_eas", 32)) := by
  exact Layout.decodeSite (pc := (⟨823⟩ : UInt256)) (words := immWords)
    824 "_eas" [] [(1719, immWords "_eas"), (1888, immWords "_eas"), (2289, immWords "_eas")]
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

/-- Final stack for bytecode block summary `attesterRuntime_block_575`. -/
def attesterRuntime_block_575_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 575. -/
theorem attesterRuntime_block_575 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_575_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((11))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨575⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨576⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨577⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨578⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨579⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 581)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_575_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_575_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_575 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem attesterRuntime_block_581_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 672) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨581⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨582⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨583⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨584⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨585⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 672) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨586⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 672), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨589⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 672)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_581_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 672) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_581_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem attesterRuntime_block_581_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨581⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨582⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨583⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨584⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨585⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 672) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨586⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 672), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨589⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 590)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_581_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_581_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_590_taken`. -/
def attesterRuntime_block_590_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_590_taken`. -/
def attesterRuntime_block_590_taken_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem attesterRuntime_block_590_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 618) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (attesterRuntime_block_590_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((55) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨590⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨592⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨593⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨594⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨596⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨597⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨599⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨600⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨601⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨602⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨603⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨604⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨605⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨606⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 618) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨607⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 618), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨610⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 618)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_590_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 618) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (attesterRuntime_block_590_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_590_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_590_fallthrough`. -/
def attesterRuntime_block_590_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_590_fallthrough`. -/
def attesterRuntime_block_590_fallthrough_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem attesterRuntime_block_590_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) (attesterRuntime_block_590_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((55) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨590⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨592⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨593⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨594⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨596⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨597⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨599⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨600⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨601⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨602⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨603⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨604⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨605⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨606⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 618) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨607⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 618), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨610⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 611)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_590_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) (attesterRuntime_block_590_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_590_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_611`. -/
def attesterRuntime_block_611_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 618) :: R)

/-- Automatically generated RD summary for bytecode block at pc 611. -/
theorem attesterRuntime_block_611 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_611_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 618) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨611⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 618), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2743) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨614⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨617⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2743)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_611_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_611_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_611 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_618_taken`. -/
def attesterRuntime_block_618_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x6 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_618_taken`. -/
def attesterRuntime_block_618_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 618. -/
theorem attesterRuntime_block_618_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 653) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (attesterRuntime_block_618_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨618⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨619⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨620⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨621⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨623⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨624⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldataload (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨625⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨626⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨627⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨628⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨630⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨631⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨633⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨634⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨635⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨636⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨637⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨638⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMload r18 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨639⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨640⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨641⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 653) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨642⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 653), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨645⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 653)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_618_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 653) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (attesterRuntime_block_618_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_618_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_618_fallthrough`. -/
def attesterRuntime_block_618_fallthrough_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x6 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_618_fallthrough`. -/
def attesterRuntime_block_618_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 618. -/
theorem attesterRuntime_block_618_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) (attesterRuntime_block_618_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨618⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨619⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨620⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨621⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨623⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨624⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldataload (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨625⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨626⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨627⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨628⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨630⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨631⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨633⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨634⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨635⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨636⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨637⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨638⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMload r18 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨639⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨640⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨641⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 653) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨642⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 653), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨645⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 646)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_618_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) (attesterRuntime_block_618_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_618_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_646`. -/
def attesterRuntime_block_646_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 653) :: R)

/-- Automatically generated RD summary for bytecode block at pc 646. -/
theorem attesterRuntime_block_646 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_646_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 653) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨646⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 653), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2743) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨649⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨652⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2743)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_646_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_646_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_646 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_653`. -/
def attesterRuntime_block_653_stack {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x3) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_653`. -/
def attesterRuntime_block_653_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 653. -/
theorem attesterRuntime_block_653 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 581) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_653_stack (x3 := x3) (R := R)) (attesterRuntime_block_653_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((50) + (memExpansionCost aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨653⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨654⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨656⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨657⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨658⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨659⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨660⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨661⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨662⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨663⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨664⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨665⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨667⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 581) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨668⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 581), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨671⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 581)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_653_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 581) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_653_stack (x3 := x3) (R := R)) (attesterRuntime_block_653_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_653 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_672_taken`. -/
def attesterRuntime_block_672_taken_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x10 :: x11 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_672_taken`. -/
def attesterRuntime_block_672_taken_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 672. -/
theorem attesterRuntime_block_672_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 702) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (attesterRuntime_block_672_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨672⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨673⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨674⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨676⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨677⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨678⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨680⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨681⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨683⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨684⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨685⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨686⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨687⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨688⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨689⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨690⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 702) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 702), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨694⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 702)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_672_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 702) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (attesterRuntime_block_672_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_672_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_672_fallthrough`. -/
def attesterRuntime_block_672_fallthrough_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x10 :: x11 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_672_fallthrough`. -/
def attesterRuntime_block_672_fallthrough_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 672. -/
theorem attesterRuntime_block_672_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) (attesterRuntime_block_672_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨672⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨673⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨674⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨676⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨677⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨678⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨680⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨681⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨683⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨684⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨685⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨686⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨687⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨688⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨689⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨690⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 702) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 702), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨694⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 695)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_672_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) (attesterRuntime_block_672_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_672_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_695`. -/
def attesterRuntime_block_695_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 702) :: R)

/-- Automatically generated RD summary for bytecode block at pc 695. -/
theorem attesterRuntime_block_695 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_695_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 702) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨695⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 702), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2743) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨698⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨701⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2743)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_695_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_695_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_695 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_702_taken`. -/
def attesterRuntime_block_702_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_702_taken`. -/
def attesterRuntime_block_702_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 702. -/
theorem attesterRuntime_block_702_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 736) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (attesterRuntime_block_702_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨702⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨703⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨704⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨705⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨707⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨708⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldataload (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨709⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨710⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨711⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨712⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨714⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨715⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨716⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨717⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨718⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨719⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨720⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨721⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMload r18 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨722⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨723⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨724⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 736) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨725⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 736), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨728⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 736)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_702_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 736) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (attesterRuntime_block_702_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_702_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_702_fallthrough`. -/
def attesterRuntime_block_702_fallthrough_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_702_fallthrough`. -/
def attesterRuntime_block_702_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 702. -/
theorem attesterRuntime_block_702_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) (attesterRuntime_block_702_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨702⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨703⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨704⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨705⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨707⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨708⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldataload (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨709⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨710⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨711⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨712⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨714⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨715⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨716⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨717⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨718⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨719⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨720⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨721⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMload r18 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨722⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨723⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨724⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 736) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨725⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 736), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨728⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 729)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_702_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) (attesterRuntime_block_702_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_702_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_729`. -/
def attesterRuntime_block_729_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 736) :: R)

/-- Automatically generated RD summary for bytecode block at pc 729. -/
theorem attesterRuntime_block_729 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_729_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 736) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨729⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 736), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2743) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨732⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨735⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2743)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_729_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_729_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_729 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_736`. -/
def attesterRuntime_block_736_stack {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x7) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_736`. -/
def attesterRuntime_block_736_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 736. -/
theorem attesterRuntime_block_736 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 367) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_736_stack (x7 := x7) (R := R)) (attesterRuntime_block_736_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((62) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨736⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨737⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.mul (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨739⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨740⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨742⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨743⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨744⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨745⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨746⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨747⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨748⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨749⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨750⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨751⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨752⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨753⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨755⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨756⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨757⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 367) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨758⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 367), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨761⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 367)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_736_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 367) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_736_stack (x7 := x7) (R := R)) (attesterRuntime_block_736_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_736 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_762`. -/
def attesterRuntime_block_762_stack {immWords : String → UInt256} {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: x1 :: (UInt256.ofNat 877) :: (UInt256.ofNat 1287121381) :: (UInt256.land (immWords "_eas") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_762`. -/
def attesterRuntime_block_762_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 762. -/
theorem attesterRuntime_block_762 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2894) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (attesterRuntime_block_762_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_762_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((65) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨762⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨763⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨764⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨766⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨767⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨800⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨801⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨802⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pushConst (immWords "_eas") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨823⟩ : UInt256)
    exact immutableDecode_823 immWords) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨856⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨857⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push4 (UInt256.ofNat 1287121381) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨858⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1287121381), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨863⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 877) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨864⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 877), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨867⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨868⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨869⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨870⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨872⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 2894) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨873⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2894), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨876⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2894)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_762_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2894) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (attesterRuntime_block_762_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_762_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_762 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_877_taken`. -/
def attesterRuntime_block_877_taken_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 877. -/
theorem attesterRuntime_block_877_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 903) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (attesterRuntime_block_877_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨877⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨878⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨880⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨882⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨883⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨884⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨885⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨886⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨887⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨889⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨890⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := r11.extcodesize (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨891⟩ : UInt256), UInt8.ofNat 59, .EXTCODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨892⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨893⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨894⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 903) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨895⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 903), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨898⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 903)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_877_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 903) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (attesterRuntime_block_877_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := attesterRuntime_block_877_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_877_fallthrough`. -/
def attesterRuntime_block_877_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 877. -/
theorem attesterRuntime_block_877_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 899) (attesterRuntime_block_877_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨877⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨878⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨880⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨882⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨883⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨884⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨885⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨886⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨887⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨889⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨890⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := r11.extcodesize (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨891⟩ : UInt256), UInt8.ofNat 59, .EXTCODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨892⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨893⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨894⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 903) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨895⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 903), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨898⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 899)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_877_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 899) (attesterRuntime_block_877_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := attesterRuntime_block_877_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
