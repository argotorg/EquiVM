import Reasoning.Reach
import Benchmarks.Safe.Runs1e6.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_1563`. -/
def safeRuntime_block_1563_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((keccakWord (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1563`. -/
def safeRuntime_block_1563_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1563. -/
theorem safeRuntime_block_1563 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 974) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1563) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 974) (safeRuntime_block_1563_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_1563_memory (ee := ee) (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) rdata σ (k + 26) (C + ((75) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) + (30 + 6 * (((UInt256.ofNat 96).toNat + 31) / 32)))) := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 974) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1563) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 974) (safeRuntime_block_1563_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_1563_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1563 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1626_taken`. -/
def safeRuntime_block_1626_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1626. -/
theorem safeRuntime_block_1626_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1637) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1637) (safeRuntime_block_1626_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1637) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1637) (safeRuntime_block_1626_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1626_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1626_fallthrough`. -/
def safeRuntime_block_1626_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1626. -/
theorem safeRuntime_block_1626_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1634) (safeRuntime_block_1626_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1626) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1634) (safeRuntime_block_1626_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1626_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1634. -/
theorem safeRuntime_block_1634 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1634) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13639) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (safeRuntime_block_1637_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 664) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1652) (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13639) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13639)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1637_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13639) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (safeRuntime_block_1637_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1637 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1652. -/
theorem safeRuntime_block_1652 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7903) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1652) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7903) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7903) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7903)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1652_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7903) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1652) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7903) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1652 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1657_taken`. -/
def safeRuntime_block_1657_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1657. -/
theorem safeRuntime_block_1657_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1668) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1668) (safeRuntime_block_1657_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1668) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1668) (safeRuntime_block_1657_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1657_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1657_fallthrough`. -/
def safeRuntime_block_1657_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1657. -/
theorem safeRuntime_block_1657_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1665) (safeRuntime_block_1657_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1657) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1665) (safeRuntime_block_1657_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1657_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1665. -/
theorem safeRuntime_block_1665 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1665) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13724) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (safeRuntime_block_1668_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 664) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1683) (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 13724) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13724)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1668_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13724) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (safeRuntime_block_1668_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1668 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1683. -/
theorem safeRuntime_block_1683 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7967) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1683) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7967) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7967) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7967)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1683_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 7967) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1683) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7967) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1683 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1688_taken`. -/
def safeRuntime_block_1688_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1688. -/
theorem safeRuntime_block_1688_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1699) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1699) (safeRuntime_block_1688_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 1699) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1699) (safeRuntime_block_1688_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1688_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1688_fallthrough`. -/
def safeRuntime_block_1688_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 1688. -/
theorem safeRuntime_block_1688_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1696) (safeRuntime_block_1688_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
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
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1696) (safeRuntime_block_1688_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1688_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1696. -/
theorem safeRuntime_block_1696 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_1699`. -/
def safeRuntime_block_1699_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 918) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1699`. -/
def safeRuntime_block_1699_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 22244971583328775298354625092596804128336193909055175729331137159030942728192).toByteArray.write 0 ((UInt256.ofNat 5).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1699. -/
theorem safeRuntime_block_1699 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 918) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1699) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 918) (safeRuntime_block_1699_stack (mem := mem) (R := R)) (safeRuntime_block_1699_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)))) := by
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
  have r17 := r16.pushConst (UInt256.ofNat 22244971583328775298354625092596804128336193909055175729331137159030942728192) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 918)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1699_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 918) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1699) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 918) (safeRuntime_block_1699_stack (mem := mem) (R := R)) (safeRuntime_block_1699_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1699 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1760`. -/
def safeRuntime_block_1760_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1768) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1760. -/
theorem safeRuntime_block_1760 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8219) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) (safeRuntime_block_1760_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1768) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8219) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8219)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1760_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8219) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) (safeRuntime_block_1760_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1760 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1768`. -/
def safeRuntime_block_1768_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 1777) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1768. -/
theorem safeRuntime_block_1768 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8269) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1768) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8269) (safeRuntime_block_1768_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1777) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8269) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8269)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1768_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8269) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1768) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8269) (safeRuntime_block_1768_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_1768 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1777`. -/
def safeRuntime_block_1777_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1924) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 3) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_1777`. -/
def safeRuntime_block_1777_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1777. -/
theorem safeRuntime_block_1777 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13831) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1777) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13831) (safeRuntime_block_1777_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_1777_memory (mem := mem) (x1 := x1)) (M (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.swap4 (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.swap5 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.swap4 (by native_decide) (by evm_ov)
  have r27 := r26.dup5 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.or (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sstore r31 hperm (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.dup4 (by native_decide) (by evm_ov)
  have r35 := RD.genMstore r34 (by native_decide) (by evm_ov)
  have r36 := r35.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r37⟩ := RD.sload r36 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap2 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.or (by native_decide) (by evm_ov)
  have r42 := r41.swap1 (by native_decide) (by evm_ov)
  have r43 := r42.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r44⟩ := RD.sstore r43 hperm (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r46 := r45.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r47⟩ := RD.sload r46 (by native_decide) (by evm_ov)
  have r48 := r47.swap1 (by native_decide) (by evm_ov)
  have r49 := r48.swap2 (by native_decide) (by evm_ov)
  have r50 := r49.swap1 (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 1924) (by native_decide) (by evm_ov)
  have r52 := r51.swap1 (by native_decide) (by evm_ov)
  have r53 := r52.push2 (UInt256.ofNat 13831) (by native_decide) (by evm_ov)
  have r54 := r53.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13831)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1777_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13831) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1777) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13831) (safeRuntime_block_1777_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_1777_memory (mem := mem) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1777 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1924_taken`. -/
def safeRuntime_block_1924_taken_stack {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1924. -/
theorem safeRuntime_block_1924_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2010) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1924) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2010) (safeRuntime_block_1924_taken_stack (x3 := x3) (x4 := x4) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 67122478919787364685654830015034087172357047607870547473226416422428542691878) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.genLog2 r15 (by native_decide) hperm (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.eq (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 2010) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2010)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1924_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 2010) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1924) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2010) (safeRuntime_block_1924_taken_stack (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1924_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_1924_fallthrough`. -/
def safeRuntime_block_1924_fallthrough_stack {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1924. -/
theorem safeRuntime_block_1924_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1924) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2002) (safeRuntime_block_1924_fallthrough_stack (x3 := x3) (x4 := x4) (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 67122478919787364685654830015034087172357047607870547473226416422428542691878) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.genLog2 r15 (by native_decide) hperm (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.eq (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 2010) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2002)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_1924_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x3) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 1924) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 2002) (safeRuntime_block_1924_fallthrough_stack (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_1924_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.Runs1e6.RuntimeBlocks
