import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode
import Benchmarks.Morpho.MetaMorphoV1_1.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1Blocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.sites = [(8892, 32, "_asset"), (9554, 32, "_asset"), (14624, 32, "_asset"), (15675, 32, "_asset"), (9752, 32, "_underlyingDecimals"), (12952, 32, "_cachedDomainSeparator"), (13141, 32, "_cachedChainId"), (12898, 32, "_cachedThis"), (13031, 32, "_hashedName"), (13069, 32, "_hashedVersion"), (4899, 32, "_name"), (4940, 32, "_version"), (6184, 32, "MORPHO"), (6494, 32, "MORPHO"), (8484, 32, "MORPHO"), (9021, 32, "MORPHO"), (9486, 32, "MORPHO"), (12214, 32, "MORPHO"), (13651, 32, "MORPHO"), (13860, 32, "MORPHO"), (14958, 32, "MORPHO"), (15902, 32, "MORPHO"), (16145, 32, "MORPHO"), (17851, 32, "MORPHO"), (18804, 32, "MORPHO"), (19479, 32, "MORPHO"), (3680, 32, "DECIMALS_OFFSET"), (9716, 32, "DECIMALS_OFFSET"), (14387, 32, "DECIMALS_OFFSET"), (14457, 32, "DECIMALS_OFFSET"), (15259, 32, "DECIMALS_OFFSET"), (15326, 32, "DECIMALS_OFFSET")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.inBounds Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords).size = Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10520_taken`. -/
def metaMorphoV1_1_block_10520_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10520. -/
theorem metaMorphoV1_1_block_10520_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10587) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10520) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10587) (metaMorphoV1_1_block_10520_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 8) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10520⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 8), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10522⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10523⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10525⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10527⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10529⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10530⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10531⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10532⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10533⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10534⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10535⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 10587) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10536⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10587), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10539⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10587)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10520_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10587) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10520) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10587) (metaMorphoV1_1_block_10520_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10520_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10520_fallthrough`. -/
def metaMorphoV1_1_block_10520_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10520. -/
theorem metaMorphoV1_1_block_10520_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10520) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1_block_10520_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 8) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10520⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 8), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10522⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10523⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10525⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10527⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10529⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10530⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10531⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10532⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10533⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10534⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10535⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 10587) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10536⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10587), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10539⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10540)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10520_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10520) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1_block_10520_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10520_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10540_taken`. -/
def metaMorphoV1_1_block_10540_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 10540. -/
theorem metaMorphoV1_1_block_10540_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 2137) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 2137) (metaMorphoV1_1_block_10540_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10540⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2137) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10541⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2137), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10544⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2137)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10540_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 2137) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 2137) (metaMorphoV1_1_block_10540_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10540_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10540_fallthrough`. -/
def metaMorphoV1_1_block_10540_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 10540. -/
theorem metaMorphoV1_1_block_10540_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10545) (metaMorphoV1_1_block_10540_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10540⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2137) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10541⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2137), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10544⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10545)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10540_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10545) (metaMorphoV1_1_block_10540_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10540_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10545. -/
theorem metaMorphoV1_1_block_10545 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10545) R mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 15) (⟨0⟩ : UInt256)) ByteArray.empty := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10545⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 15) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10546⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10548⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10549⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 88671044509120175682419812806829133751554734994516651254244353853562900567651) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10550⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 88671044509120175682419812806829133751554734994516651254244353853562900567651), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10583⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10584⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genLog2 r7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10585⟩ : UInt256), UInt8.ofNat 162, .LOG2, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  exact r8.stop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10586⟩ : UInt256), UInt8.ofNat 0, .STOP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10587`. -/
def metaMorphoV1_1_block_10587_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10587. -/
theorem metaMorphoV1_1_block_10587 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10540) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10587) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1_block_10587_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10587⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10588⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 12) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10589⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10591⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10592⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10594⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10596⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10598⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10599⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10600⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10601⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10602⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10603⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 10540) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10604⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10540), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10607⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10540)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10587_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10540) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10587) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1_block_10587_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10587 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10608. -/
theorem metaMorphoV1_1_block_10608_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10608) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10608⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10609⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10608_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10608) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10608_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10608. -/
theorem metaMorphoV1_1_block_10608_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10608) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10608⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10609⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10614)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10608_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10608) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10608_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10614. -/
theorem metaMorphoV1_1_block_10614_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10614⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10615⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10616⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10618⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10619⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10620⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10624⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10614_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10614_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10614. -/
theorem metaMorphoV1_1_block_10614_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10625) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10614⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10615⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10616⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10618⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10619⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10620⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10624⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10625)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10614_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10614) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10625) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10614_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10625. -/
theorem metaMorphoV1_1_block_10625 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10625) R mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10625⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10627⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10629⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10630⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10632⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10633⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10634⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10635⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10636⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 10637. -/
theorem metaMorphoV1_1_block_10637_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10637) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10637⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10638⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10639⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10642⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10637_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10637) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10637_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10637. -/
theorem metaMorphoV1_1_block_10637_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10637) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10637⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10638⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10639⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10642⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10643)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10637_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10637) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10637_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10643. -/
theorem metaMorphoV1_1_block_10643_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10643⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10645⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10646⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10648⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10649⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10650⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10651⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10654⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10643_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10643_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10643. -/
theorem metaMorphoV1_1_block_10643_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10643⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10645⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10646⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10648⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10649⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10650⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10651⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10654⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10655)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10643_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10643) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10643_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10655_taken`. -/
def metaMorphoV1_1_block_10655_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10655. -/
theorem metaMorphoV1_1_block_10655_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10761) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10761) (metaMorphoV1_1_block_10655_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10655⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10657⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10658⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10660⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10663⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10664⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 12) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10665⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10667⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10668⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10669⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10670⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10671⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10672⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 10761) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10673⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10761), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10676⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10761)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10655_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10761) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10761) (metaMorphoV1_1_block_10655_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10655_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10655_fallthrough`. -/
def metaMorphoV1_1_block_10655_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10655. -/
theorem metaMorphoV1_1_block_10655_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (metaMorphoV1_1_block_10655_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10655⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10657⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10658⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10660⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10663⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10664⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 12) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10665⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10667⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10668⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10669⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10670⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10671⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10672⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 10761) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10673⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10761), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10676⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10677)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10655_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10655) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (metaMorphoV1_1_block_10655_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10655_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10677. -/
theorem metaMorphoV1_1_block_10677_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10740) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10740) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10677⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10678⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10740) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10679⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10740), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10682⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10740)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10677_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10740) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10740) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10677_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10677. -/
theorem metaMorphoV1_1_block_10677_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10677⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10678⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10740) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10679⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10740), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10682⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10683)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10677_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10677_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10683_taken`. -/
def metaMorphoV1_1_block_10683_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 10683. -/
theorem metaMorphoV1_1_block_10683_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 7782) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 7782) (metaMorphoV1_1_block_10683_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10683⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7782) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10684⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7782), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10687⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7782)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10683_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 7782) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 7782) (metaMorphoV1_1_block_10683_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10683_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1Blocks
