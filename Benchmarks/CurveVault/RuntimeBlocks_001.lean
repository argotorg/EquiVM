import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_0_taken`. -/
def vault_block_0_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) :: (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `vault_block_0_taken`. -/
def vault_block_0_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem vault_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.gt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 3)) (UInt256.eq (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6768) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6768) (vault_block_0_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_0_taken_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 53) (C + ((165) + (memExpansionCost aw (UInt256.ofNat 27) (UInt256.ofNat 5)) + (3 + 3 * (((UInt256.ofNat 5).toNat + 31) / 32)) + (memExpansionCost (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) + (3 + 3 * (((UInt256.ofNat 7).toNat + 31) / 32)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.mod (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8288) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 27) (by native_decide) (by evm_ov)
  have r14 := RD.genCodecopy r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.dup5 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r25 := r24.shr (by native_decide) (by evm_ov)
  have r26 := r25.mul (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r28 := r27.shr (by native_decide) (by evm_ov)
  have r29 := r28.mod (by native_decide) (by evm_ov)
  have r30 := r29.mul (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r33 := r32.shr (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 25) (by native_decide) (by evm_ov)
  have r38 := RD.genCodecopy r37 (by native_decide) (by evm_ov)
  have r39 := r38.pop (by native_decide) (by evm_ov)
  have r40 := r39.push0 (by native_decide) (by evm_ov)
  have r41 := RD.genMload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.dup2 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r45 := r44.shr (by native_decide) (by evm_ov)
  have r46 := r45.eq (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r48 := r47.calldatasize (by native_decide) (by evm_ov)
  have r49 := r48.gt (by native_decide) (by evm_ov)
  have r50 := r49.and (by native_decide) (by evm_ov)
  have r51 := r50.iszero (by native_decide) (by evm_ov)
  have r52 := r51.push2 (UInt256.ofNat 6768) (by native_decide) (by evm_ov)
  have r53 := r52.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6768)) r53 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_0_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.gt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 3)) (UInt256.eq (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6768) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6768) (vault_block_0_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_0_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_0_fallthrough`. -/
def vault_block_0_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) :: (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `vault_block_0_fallthrough`. -/
def vault_block_0_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem vault_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.gt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 3)) (UInt256.eq (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (vault_block_0_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_0_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 53) (C + ((165) + (memExpansionCost aw (UInt256.ofNat 27) (UInt256.ofNat 5)) + (3 + 3 * (((UInt256.ofNat 5).toNat + 31) / 32)) + (memExpansionCost (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) + (3 + 3 * (((UInt256.ofNat 7).toNat + 31) / 32)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 27) (UInt256.ofNat 5)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 25) (UInt256.ofNat 7)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.mod (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8288) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 27) (by native_decide) (by evm_ov)
  have r14 := RD.genCodecopy r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.dup5 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r25 := r24.shr (by native_decide) (by evm_ov)
  have r26 := r25.mul (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r28 := r27.shr (by native_decide) (by evm_ov)
  have r29 := r28.mod (by native_decide) (by evm_ov)
  have r30 := r29.mul (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r33 := r32.shr (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 25) (by native_decide) (by evm_ov)
  have r38 := RD.genCodecopy r37 (by native_decide) (by evm_ov)
  have r39 := r38.pop (by native_decide) (by evm_ov)
  have r40 := r39.push0 (by native_decide) (by evm_ov)
  have r41 := RD.genMload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.dup2 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r45 := r44.shr (by native_decide) (by evm_ov)
  have r46 := r45.eq (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r48 := r47.calldatasize (by native_decide) (by evm_ov)
  have r49 := r48.gt (by native_decide) (by evm_ov)
  have r50 := r49.and (by native_decide) (by evm_ov)
  have r51 := r50.iszero (by native_decide) (by evm_ov)
  have r52 := r51.push2 (UInt256.ofNat 6768) (by native_decide) (by evm_ov)
  have r53 := r52.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 73)) r53 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_0_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.gt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 3)) (UInt256.eq (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 8))) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (UInt256.mul (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) (UInt256.ofNat 24)) (UInt256.land (UInt256.ofNat 255) (memLoad (⟨0⟩ : UInt256) (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat)))) (UInt256.ofNat 7))).toNat (Benchmarks.CurveVault.vaultBytecode.write ((UInt256.ofNat 8288) + (UInt256.mul (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 5)) (UInt256.ofNat 5))).toNat mem (UInt256.ofNat 27).toNat (UInt256.ofNat 5).toNat) (UInt256.ofNat 25).toNat (UInt256.ofNat 7).toNat)) (UInt256.ofNat 24)) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (vault_block_0_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_0_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 73. -/
theorem vault_block_73_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 1) x0) ee.weiValue) (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.land (UInt256.ofNat 254) x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (x0 :: R) mem aw rdata σ (k + 13) (C + ((46))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 254) (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.callvalue (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.or (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_73_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 1) x0) ee.weiValue) (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.land (UInt256.ofNat 254) x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_73_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 73. -/
theorem vault_block_73_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 1) x0) ee.weiValue) (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.land (UInt256.ofNat 254) x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 90) (x0 :: R) mem aw rdata σ (k + 13) (C + ((46))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 254) (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.callvalue (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.or (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 90)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_73_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.mul (UInt256.land (UInt256.ofNat 1) x0) ee.weiValue) (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.land (UInt256.ofNat 254) x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 73) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 90) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_73_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 90. -/
theorem vault_block_90 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x0 (UInt256.ofNat 8))) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 90) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x0 (UInt256.ofNat 8))) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r3 := r2.shr (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_90_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x0 (UInt256.ofNat 8))) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 90) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x0 (UInt256.ofNat 8))) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_90 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 99. -/
theorem vault_block_99 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 110. -/
theorem vault_block_110 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 110) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 122. -/
theorem vault_block_122 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 122) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 134. -/
theorem vault_block_134 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 134) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 146. -/
theorem vault_block_146 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 146) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_158_taken`. -/
def vault_block_158_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 158. -/
theorem vault_block_158_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 158) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_158_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_158_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 158) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_158_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_158_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_158_fallthrough`. -/
def vault_block_158_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 158. -/
theorem vault_block_158_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 158) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (vault_block_158_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 170)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_158_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 158) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (vault_block_158_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_158_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_170_taken`. -/
def vault_block_170_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_170_taken`. -/
def vault_block_170_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 170. -/
theorem vault_block_170_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_170_taken_stack (ee := ee) (R := R)) (vault_block_170_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_170_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_170_taken_stack (ee := ee) (R := R)) (vault_block_170_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_170_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_170_fallthrough`. -/
def vault_block_170_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_170_fallthrough`. -/
def vault_block_170_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 170. -/
theorem vault_block_170_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (vault_block_170_fallthrough_stack (ee := ee) (R := R)) (vault_block_170_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 184)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_170_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 170) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (vault_block_170_fallthrough_stack (ee := ee) (R := R)) (vault_block_170_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_170_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_184_taken`. -/
def vault_block_184_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_184_taken`. -/
def vault_block_184_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 184. -/
theorem vault_block_184_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_184_taken_stack (ee := ee) (R := R)) (vault_block_184_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_184_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_184_taken_stack (ee := ee) (R := R)) (vault_block_184_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_184_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_184_fallthrough`. -/
def vault_block_184_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_184_fallthrough`. -/
def vault_block_184_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 184. -/
theorem vault_block_184_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (vault_block_184_fallthrough_stack (ee := ee) (R := R)) (vault_block_184_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 198)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_184_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 184) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (vault_block_184_fallthrough_stack (ee := ee) (R := R)) (vault_block_184_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_184_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_198_taken`. -/
def vault_block_198_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_198_taken`. -/
def vault_block_198_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 198. -/
theorem vault_block_198_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_198_taken_stack (ee := ee) (R := R)) (vault_block_198_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_198_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_198_taken_stack (ee := ee) (R := R)) (vault_block_198_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_198_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_198_fallthrough`. -/
def vault_block_198_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_198_fallthrough`. -/
def vault_block_198_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 198. -/
theorem vault_block_198_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (vault_block_198_fallthrough_stack (ee := ee) (R := R)) (vault_block_198_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 212)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_198_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 198) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (vault_block_198_fallthrough_stack (ee := ee) (R := R)) (vault_block_198_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_198_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_212_taken`. -/
def vault_block_212_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_212_taken`. -/
def vault_block_212_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 212. -/
theorem vault_block_212_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_212_taken_stack (R := R)) (vault_block_212_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_212_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_212_taken_stack (R := R)) (vault_block_212_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_212_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_212_fallthrough`. -/
def vault_block_212_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_212_fallthrough`. -/
def vault_block_212_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 212. -/
theorem vault_block_212_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 221) (vault_block_212_fallthrough_stack (R := R)) (vault_block_212_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 221)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_212_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 212) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 221) (vault_block_212_fallthrough_stack (R := R)) (vault_block_212_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_212_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vaultBlocks
