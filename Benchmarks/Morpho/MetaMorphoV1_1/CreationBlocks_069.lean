import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 14362. -/
theorem metaMorphoV1_1Creation_block_14362 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14362) R mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 23) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 23) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 14374. -/
theorem metaMorphoV1_1Creation_block_14374_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14374) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14374_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14374) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14374_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14374. -/
theorem metaMorphoV1_1Creation_block_14374_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14374) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14380)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14374_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14374) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14374_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14380. -/
theorem metaMorphoV1_1Creation_block_14380_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14380_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14380_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14380. -/
theorem metaMorphoV1_1Creation_block_14380_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14391)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14380_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14380) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14380_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14391_taken`. -/
def metaMorphoV1_1Creation_block_14391_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14391. -/
theorem metaMorphoV1_1Creation_block_14391_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10587) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10587) (metaMorphoV1_1Creation_block_14391_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 8) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 10587) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 10587) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10587)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14391_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10587) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10587) (metaMorphoV1_1Creation_block_14391_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_14391_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14391_fallthrough`. -/
def metaMorphoV1_1Creation_block_14391_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14391. -/
theorem metaMorphoV1_1Creation_block_14391_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (metaMorphoV1_1Creation_block_14391_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 8) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 10587) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14411)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14391_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14391) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (metaMorphoV1_1Creation_block_14391_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_14391_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14411_taken`. -/
def metaMorphoV1_1Creation_block_14411_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14411. -/
theorem metaMorphoV1_1Creation_block_14411_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2137) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2137) (metaMorphoV1_1Creation_block_14411_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2137) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 2137) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2137)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14411_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 2137) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2137) (metaMorphoV1_1Creation_block_14411_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14411_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14411_fallthrough`. -/
def metaMorphoV1_1Creation_block_14411_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14411. -/
theorem metaMorphoV1_1Creation_block_14411_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14416) (metaMorphoV1_1Creation_block_14411_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2137) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14416)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14411_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14416) (metaMorphoV1_1Creation_block_14411_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14411_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14416. -/
theorem metaMorphoV1_1Creation_block_14416 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14416) R mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 15) (⟨0⟩ : UInt256)) ByteArray.empty := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 15) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 88671044509120175682419812806829133751554734994516651254244353853562900567651) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genLog2 r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  exact r8.stop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1Creation_block_14458`. -/
def metaMorphoV1_1Creation_block_14458_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14458. -/
theorem metaMorphoV1_1Creation_block_14458 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10540) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14458) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1Creation_block_14458_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 10540) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 10540) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10540)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14458_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 10540) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14458) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10540) (metaMorphoV1_1Creation_block_14458_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1Creation_block_14458 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14479. -/
theorem metaMorphoV1_1Creation_block_14479_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14479) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14479_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14479) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14479_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14479. -/
theorem metaMorphoV1_1Creation_block_14479_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14479) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14485)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14479_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14479) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14479_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14485. -/
theorem metaMorphoV1_1Creation_block_14485_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14485_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14485_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14485. -/
theorem metaMorphoV1_1Creation_block_14485_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14496) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14496)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14485_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14485) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14496) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14485_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14496. -/
theorem metaMorphoV1_1Creation_block_14496 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14496) R mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 14508. -/
theorem metaMorphoV1_1Creation_block_14508_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14508) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14508_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14508) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14508_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14508. -/
theorem metaMorphoV1_1Creation_block_14508_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14508) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14514)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14508_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14508) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14508_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14514. -/
theorem metaMorphoV1_1Creation_block_14514_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 917) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14514_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14514_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14514. -/
theorem metaMorphoV1_1Creation_block_14514_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14526) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode.size = 23633 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14526)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1Creation_block_14514_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14514) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1CreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14526) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1Creation_block_14514_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1CreationBlocks
