import Reasoning.Reach
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeRuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_1563`. -/
def safeRuntime_block_1563_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((keccakWord (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1563`. -/
def safeRuntime_block_1563_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1563. -/
theorem safeRuntime_block_1563 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 974) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1563) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 974) (safeRuntime_block_1563_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_1563_memory (ee := ee) (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) rdata σ (k + 26) (C + ((75) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) + (30 + 6 * (((UInt256.ofNat 96).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.chainid (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.address (by native_decide) (by evm_ov)
  have r15 := r14.swap2 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 974) (by native_decide) (by evm_ov)
  have r26 := r25.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 974)) r26 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1563_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 974) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1563) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 974) (safeRuntime_block_1563_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_1563_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1563 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1626_taken`. -/
def safeRuntime_block_1626_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1626. -/
theorem safeRuntime_block_1626_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1637) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1637) (safeRuntime_block_1626_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1637) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1637)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1626_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1637) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1637) (safeRuntime_block_1626_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1626_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1626_fallthrough`. -/
def safeRuntime_block_1626_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1626. -/
theorem safeRuntime_block_1626_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1634) (safeRuntime_block_1626_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1637) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1634)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1626_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1634) (safeRuntime_block_1626_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1626_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1634. -/
theorem safeRuntime_block_1634 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1634) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_1637`. -/
def safeRuntime_block_1637_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 1652) :: (UInt256.ofNat 664) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1637. -/
theorem safeRuntime_block_1637 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 10995) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 10995) (safeRuntime_block_1637_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 664) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1652) (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10995) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10995)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1637_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 10995) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 10995) (safeRuntime_block_1637_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1637 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1652. -/
theorem safeRuntime_block_1652 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6526) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1652) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6526) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6526) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6526)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1652_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6526) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1652) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6526) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1652 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1657_taken`. -/
def safeRuntime_block_1657_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1657. -/
theorem safeRuntime_block_1657_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1668) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1668) (safeRuntime_block_1657_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1668) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1668)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1657_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1668) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1668) (safeRuntime_block_1657_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1657_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1657_fallthrough`. -/
def safeRuntime_block_1657_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1657. -/
theorem safeRuntime_block_1657_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1665) (safeRuntime_block_1657_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1668) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1665)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1657_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1665) (safeRuntime_block_1657_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1657_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1665. -/
theorem safeRuntime_block_1665 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1665) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_1668`. -/
def safeRuntime_block_1668_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 1683) :: (UInt256.ofNat 664) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1668. -/
theorem safeRuntime_block_1668 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11079) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11079) (safeRuntime_block_1668_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 664) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1683) (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11079) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11079)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1668_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11079) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11079) (safeRuntime_block_1668_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1668 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1683. -/
theorem safeRuntime_block_1683 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6566) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1683) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6566) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6566) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6566)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1683_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6566) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1683) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6566) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1683 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1688_taken`. -/
def safeRuntime_block_1688_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1688. -/
theorem safeRuntime_block_1688_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1699) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1699) (safeRuntime_block_1688_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1699) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1699)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1688_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1699) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1699) (safeRuntime_block_1688_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1688_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1688_fallthrough`. -/
def safeRuntime_block_1688_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1688. -/
theorem safeRuntime_block_1688_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1696) (safeRuntime_block_1688_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1699) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1696)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1688_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1696) (safeRuntime_block_1688_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1688_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1696. -/
theorem safeRuntime_block_1696 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_1699`. -/
def safeRuntime_block_1699_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 918) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1699`. -/
def safeRuntime_block_1699_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 13201789667) (UInt256.ofNat 220)).toByteArray.write 0 ((UInt256.ofNat 5).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1699. -/
theorem safeRuntime_block_1699 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 918) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1699) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 918) (safeRuntime_block_1699_stack (mem := mem) (R := R)) (safeRuntime_block_1699_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((73) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 918) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.pushConst (UInt256.ofNat 13201789667) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.pop (by native_decide) (by evm_ov)
  have r23 := r22.dup2 (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 918)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1699_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 918) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1699) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 918) (safeRuntime_block_1699_stack (mem := mem) (R := R)) (safeRuntime_block_1699_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1699 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1736`. -/
def safeRuntime_block_1736_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1744) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1736. -/
theorem safeRuntime_block_1736 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1736) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_1736_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1744) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6757) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6757)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1736_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6757) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1736) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6757) (safeRuntime_block_1736_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1736 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1744`. -/
def safeRuntime_block_1744_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 1753) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1744. -/
theorem safeRuntime_block_1744 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6783) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1744) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6783) (safeRuntime_block_1744_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1753) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6783) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6783)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1744_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6783) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1744) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6783) (safeRuntime_block_1744_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1744 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1753`. -/
def safeRuntime_block_1753_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1863) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 3) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1753`. -/
def safeRuntime_block_1753_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1753. -/
theorem safeRuntime_block_1753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11161) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1753) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11161) (safeRuntime_block_1753_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_1753_memory (mem := mem) (x1 := x1)) (M (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup5 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sload r23 (by native_decide) (by evm_ov)
  have r25 := r24.swap4 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.swap5 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.not (by native_decide) (by evm_ov)
  have r35 := r34.swap4 (by native_decide) (by evm_ov)
  have r36 := r35.dup5 (by native_decide) (by evm_ov)
  have r37 := r36.and (by native_decide) (by evm_ov)
  have r38 := r37.or (by native_decide) (by evm_ov)
  have r39 := r38.swap1 (by native_decide) (by evm_ov)
  have r40 := r39.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r41⟩ := RD.sstore r40 hperm (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := RD.genMstore r43 (by native_decide) (by evm_ov)
  have r45 := r44.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r46⟩ := RD.sload r45 (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.swap2 (by native_decide) (by evm_ov)
  have r49 := r48.and (by native_decide) (by evm_ov)
  have r50 := r49.or (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r53⟩ := RD.sstore r52 hperm (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r55 := r54.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r56⟩ := RD.sload r55 (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.swap2 (by native_decide) (by evm_ov)
  have r59 := r58.swap1 (by native_decide) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 1863) (by native_decide) (by evm_ov)
  have r61 := r60.swap1 (by native_decide) (by evm_ov)
  have r62 := r61.push2 (UInt256.ofNat 11161) (by native_decide) (by evm_ov)
  have r63 := r62.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11161)) r63 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1753_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11161) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1753) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11161) (safeRuntime_block_1753_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_1753_memory (mem := mem) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1753 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1863_taken`. -/
def safeRuntime_block_1863_taken_stack {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1863. -/
theorem safeRuntime_block_1863_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1863) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1936) (safeRuntime_block_1863_taken_stack (x3 := x3) (x4 := x4) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.pushConst (UInt256.ofNat 67122478919787364685654830015034087172357047607870547473226416422428542691878) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := RD.genLog2 r19 (by native_decide) hperm (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by native_decide) (by evm_ov)
  have r24 := r23.eq (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1936)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1863_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 1936) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1863) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1936) (safeRuntime_block_1863_taken_stack (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1863_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1863_fallthrough`. -/
def safeRuntime_block_1863_fallthrough_stack {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1863. -/
theorem safeRuntime_block_1863_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1863) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1928) (safeRuntime_block_1863_fallthrough_stack (x3 := x3) (x4 := x4) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.pushConst (UInt256.ofNat 67122478919787364685654830015034087172357047607870547473226416422428542691878) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := RD.genLog2 r19 (by native_decide) hperm (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by native_decide) (by evm_ov)
  have r24 := r23.eq (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1936) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1928)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1863_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1863) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 1928) (safeRuntime_block_1863_fallthrough_stack (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1863_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end safeRuntimeBlocks
