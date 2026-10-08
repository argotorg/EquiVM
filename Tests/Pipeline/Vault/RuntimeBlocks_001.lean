import Reasoning.Reach
import Reasoning.Immutables
import Tests.Pipeline.Vault.Bytecode
import Tests.Pipeline.Vault.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Tests.Pipeline.Vault.immutableLayout.sites = [(219, 32, "feeBps"), (1591, 32, "feeBps"), (325, 32, "owner"), (450, 32, "owner"), (1239, 32, "owner")] := by native_decide

theorem immutableLayout_inBounds :
    Tests.Pipeline.Vault.immutableLayout.inBounds Tests.Pipeline.Vault.vaultBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Tests.Pipeline.Vault.vaultBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords).size = Tests.Pipeline.Vault.vaultBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `vault_block_0_taken`. -/
def vault_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `vault_block_0_taken`. -/
def vault_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem vault_block_0_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 15) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (vault_block_0_taken_stack (ee := ee) (R := R)) (vault_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 15) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_0_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 15) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (vault_block_0_taken_stack (ee := ee) (R := R)) (vault_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_0_fallthrough`. -/
def vault_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `vault_block_0_fallthrough`. -/
def vault_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem vault_block_0_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 12) (vault_block_0_fallthrough_stack (ee := ee) (R := R)) (vault_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 15) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_0_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 12) (vault_block_0_fallthrough_stack (ee := ee) (R := R)) (vault_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12. -/
theorem vault_block_12 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 12) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨12⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨13⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨14⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_15_taken`. -/
def vault_block_15_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem vault_block_15_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 166) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 166) (vault_block_15_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨15⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨19⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 166) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 166), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨24⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 166)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_15_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 166) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 166) (vault_block_15_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_15_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_15_fallthrough`. -/
def vault_block_15_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem vault_block_15_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) (vault_block_15_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨15⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨19⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 166) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 166), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨24⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 25)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_15_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) (vault_block_15_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_15_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_25_taken`. -/
def vault_block_25_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem vault_block_25_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 773487949) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 110) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 110) (vault_block_25_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨27⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨30⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 773487949) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 773487949), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨36⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 110) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨37⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 110), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨40⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 110)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_25_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 773487949) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 110) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 110) (vault_block_25_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_25_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_25_fallthrough`. -/
def vault_block_25_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem vault_block_25_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 773487949) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (vault_block_25_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨27⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨30⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 773487949) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 773487949), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨36⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 110) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨37⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 110), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨40⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 41)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_25_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 773487949) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (vault_block_25_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_25_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 41. -/
theorem vault_block_41_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 773487949) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 293) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 293) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨41⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 773487949), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨47⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 293) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨48⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 293), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨51⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 293)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_41_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 773487949) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 293) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 293) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_41_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 41. -/
theorem vault_block_41_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 773487949) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨41⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 773487949), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨47⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 293) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨48⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 293), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨51⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 52)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_41_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 773487949) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_41_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 52. -/
theorem vault_block_52_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1311789167) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 312) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 312) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨52⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1311789167) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1311789167), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨58⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 312) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨59⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 312), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨62⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 312)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_52_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1311789167) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 312) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 312) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_52_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 52. -/
theorem vault_block_52_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1311789167) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨52⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1311789167) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1311789167), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨58⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 312) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨59⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 312), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨62⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 63)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_52_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1311789167) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_52_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 63. -/
theorem vault_block_63_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 320) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 320) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨63⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨64⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨69⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨70⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 320), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨73⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 320)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_63_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 320) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 320) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_63_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 63. -/
theorem vault_block_63_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨63⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨64⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨69⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨70⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 320), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨73⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 74)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_63_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_63_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 74. -/
theorem vault_block_74_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3065339685) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 383) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 383) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨74⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3065339685) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨75⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3065339685), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨80⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 383) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨81⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 383), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨84⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 383)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_74_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3065339685) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 383) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 383) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_74_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 74. -/
theorem vault_block_74_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3065339685) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨74⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3065339685) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨75⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3065339685), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨80⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 383) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨81⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 383), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨84⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 85)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_74_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3065339685) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 74) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_74_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 85. -/
theorem vault_block_85_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3836935033) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 402) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨85⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3836935033) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨86⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3836935033), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨91⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 402) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨92⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨95⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_85_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3836935033) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 402) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 402) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_85_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 85. -/
theorem vault_block_85_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3836935033) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨85⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3836935033) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨86⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3836935033), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨91⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 402) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨92⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 402), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨95⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 96)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_85_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3836935033) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 85) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_85_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 96. -/
theorem vault_block_96_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4228666474) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 421) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 421) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨96⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4228666474) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨97⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4228666474), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨102⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 421) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨103⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 421), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨106⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 421)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_96_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4228666474) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 421) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 421) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_96_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 96. -/
theorem vault_block_96_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4228666474) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 107) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨96⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4228666474) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨97⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4228666474), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨102⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 421) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨103⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 421), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨106⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 107)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_96_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4228666474) x0) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 107) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_96_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 107. -/
theorem vault_block_107 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 107) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨107⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨108⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨109⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end vaultBlocks
