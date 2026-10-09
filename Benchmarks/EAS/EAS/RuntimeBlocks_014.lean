import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.EAS.Bytecode
import Benchmarks.EAS.EAS.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace easBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.EAS.EAS.immutableLayout.sites = [(14029, 32, "_CACHED_DOMAIN_SEPARATOR"), (14218, 32, "_CACHED_CHAIN_ID"), (13982, 32, "_CACHED_THIS"), (14108, 32, "_HASHED_NAME"), (14146, 32, "_HASHED_VERSION"), (14073, 32, "_TYPE_HASH"), (678, 32, "_schemaRegistry"), (7761, 32, "_schemaRegistry"), (9982, 32, "_schemaRegistry"), (12162, 32, "_schemaRegistry"), (12821, 32, "_schemaRegistry")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.EAS.EAS.immutableLayout.inBounds Benchmarks.EAS.EAS.easBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.EAS.EAS.easBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size = Benchmarks.EAS.EAS.easBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Automatically generated RD summary for bytecode block at pc 3280. -/
theorem eas_block_3280_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3280) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) R mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3280⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3281⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3283⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3316⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3317⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3318⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3319⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3322⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3280_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3280) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3280_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3280. -/
theorem eas_block_3280_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3280) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3280⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3281⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3283⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3316⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3317⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3318⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3319⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3322⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3323)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3280_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3280) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3280_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3323_taken`. -/
def eas_block_3323_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3323. -/
theorem eas_block_3323_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3323_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3323⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3325⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3326⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3335⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3336⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3337⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3340⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3323_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3323_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3323_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3323_fallthrough`. -/
def eas_block_3323_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3323. -/
theorem eas_block_3323_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3341) (eas_block_3323_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3323⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3325⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3326⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3335⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3336⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3337⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3340⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3341)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3323_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3323) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3341) (eas_block_3323_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3323_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3341`. -/
def eas_block_3341_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 3354) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3341. -/
theorem eas_block_3341 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4225) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3341) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4225) (eas_block_3341_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3354) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3341⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3354), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3344⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3345⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3346⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3347⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3349⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 4225) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3350⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4225), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3353⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4225)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3341_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4225) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3341) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4225) (eas_block_3341_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3341 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3354`. -/
def eas_block_3354_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: x0 :: (UInt256.ofNat 0) :: x1 :: (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3354. -/
theorem eas_block_3354 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3354) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (eas_block_3354_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3354⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3355⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3388⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3389⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3390⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3391⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3392⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3394⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.callvalue (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3395⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3396)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3354_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3354) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (eas_block_3354_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3354 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3396. -/
theorem eas_block_3396_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 3405) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3405) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3396⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3397⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3398⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3399⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3405) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3400⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3405), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3403⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3405)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3396_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 3405) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3405) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3396_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3396. -/
theorem eas_block_3396_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3404) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3396⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3397⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3398⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3399⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3405) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3400⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3405), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3403⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3404)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3396_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x2 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3404) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3396_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3404. -/
theorem eas_block_3404 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3404) R mem aw rdata σ k C)
    : RDret (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) g s0 σ ByteArray.empty := by
  let r0 := h
  exact r0.stop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3404⟩ : UInt256), UInt8.ofNat 0, .STOP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `eas_block_3405`. -/
def eas_block_3405_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x1 :: x2 :: (UInt256.ofNat 3416) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3405. -/
theorem eas_block_3405 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5196) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3405) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5196) (eas_block_3405_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3405⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 3416) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3406⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3416), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3409⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3410⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3411⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5196) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3412⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5196), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3415⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5196)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3405_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5196) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3405) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5196) (eas_block_3405_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3405 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3416_taken`. -/
def eas_block_3416_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3416. -/
theorem eas_block_3416_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3416) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3416_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((49))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3416⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3417⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3419⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3420⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3421⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3422⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3455⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3456⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3457⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3458⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3459⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3460⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3461⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3462⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3465⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3416_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3416) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3416_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3416_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3416_fallthrough`. -/
def eas_block_3416_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3416. -/
theorem eas_block_3416_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3416) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (eas_block_3416_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((49))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3416⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3417⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3419⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3420⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3421⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3422⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3455⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3456⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3457⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3458⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3459⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3460⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3461⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3462⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3465⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3466)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3416_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes (x0 + (UInt256.ofNat 32)).toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3416) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (eas_block_3416_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3416_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3466_taken`. -/
def eas_block_3466_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + x0) :: x2 :: x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3466. -/
theorem eas_block_3466_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3466_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3466⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3467⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3468⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3469⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3470⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3471⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3472⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3481⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3482⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3483⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3486⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3466_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3466_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3466_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3466_fallthrough`. -/
def eas_block_3466_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + x0) :: x2 :: x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3466. -/
theorem eas_block_3466_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (eas_block_3466_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((40))) := by
  let r0 := h
  have r1 := r0.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3466⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3467⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3468⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3469⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3470⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3471⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3472⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3481⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3482⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3483⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3486⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3487)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3466_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3466) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (eas_block_3466_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3466_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3487_taken`. -/
def eas_block_3487_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x1 :: x2 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3487. -/
theorem eas_block_3487_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x3 (UInt256.ofNat 6)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3487_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 12) (C + ((42))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3487⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3489⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3490⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3491⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3492⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3494⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3495⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3496⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3497⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sgt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3498⟩ : UInt256), UInt8.ofNat 19, .SGT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3499⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3502⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3487_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x3 (UInt256.ofNat 6)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) (eas_block_3487_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3487_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3487_fallthrough`. -/
def eas_block_3487_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x1 :: x2 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3487. -/
theorem eas_block_3487_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x3 (UInt256.ofNat 6)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3503) (eas_block_3487_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 12) (C + ((42))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3487⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3489⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3490⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3491⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3492⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3494⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3495⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3496⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3497⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sgt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3498⟩ : UInt256), UInt8.ofNat 19, .SGT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3499⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3502⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3503)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3487_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x3 (UInt256.ofNat 6)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3487) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3503) (eas_block_3487_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3487_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3503`. -/
def eas_block_3503_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 3530) :: x2 :: (UInt256.ofNat ee.source.val) :: x1 :: (UInt256.eq x5 x7) :: (UInt256.ofNat 1710) :: x1 :: (UInt256.ofNat 3537) :: (UInt256.ofNat 1) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3503. -/
theorem eas_block_3503 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5924) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3503) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5924) (eas_block_3503_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 18) (C + ((57))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3503⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3505⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3506⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1710) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3507⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1710), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3510⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3537) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3511⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3537), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3514⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 3530) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3515⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3530), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3518⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3519⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.eq (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3520⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3521⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.caller (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3522⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3523⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3524⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3525⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5924) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3526⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5924), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3529⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5924)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3503_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5924) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3503) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5924) (eas_block_3503_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3503 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3530`. -/
def eas_block_3530_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3530. -/
theorem eas_block_3530 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 12743) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3530) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 12743) (eas_block_3530_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3530⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3531⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3532⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 12743) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3533⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3536⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12743)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3530_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 12743) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3530) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 12743) (eas_block_3530_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3530 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_3537`. -/
def eas_block_3537_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: (x3 + x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3537. -/
theorem eas_block_3537 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 3396) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (eas_block_3537_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3537⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3538⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3539⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3540⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3396) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3541⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3396), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3544⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3396)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3537_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 3396) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3396) (eas_block_3537_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3537 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3545. -/
theorem eas_block_3545_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3545) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) R mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3545⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3546⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3548⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3581⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3582⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3583⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 402) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3584⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨3587⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_3545_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 3545) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 402) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_3545_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end easBlocks
