import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV4PoolManager.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode

/-- Final stack for bytecode block summary `poolManagerCreation_block_11975`. -/
def poolManagerCreation_block_11975_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `poolManagerCreation_block_11975`. -/
def poolManagerCreation_block_11975_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11975. -/
theorem poolManagerCreation_block_11975 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11975) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_11975_stack (R := R)) (poolManagerCreation_block_11975_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_11975_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11975) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_11975_stack (R := R)) (poolManagerCreation_block_11975_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_11975 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_11979_taken`. -/
def poolManagerCreation_block_11979_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 160)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11979. -/
theorem poolManagerCreation_block_11979_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 7857) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11979) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7857) (poolManagerCreation_block_11979_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7857) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7857) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7857)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_11979_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 7857) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11979) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7857) (poolManagerCreation_block_11979_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_11979_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_11979_fallthrough`. -/
def poolManagerCreation_block_11979_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 160)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11979. -/
theorem poolManagerCreation_block_11979_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11979) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12003) (poolManagerCreation_block_11979_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 7857) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12003)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_11979_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11979) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12003) (poolManagerCreation_block_11979_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_11979_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12003`. -/
def poolManagerCreation_block_12003_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `poolManagerCreation_block_12003`. -/
def poolManagerCreation_block_12003_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12003. -/
theorem poolManagerCreation_block_12003 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12003) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_12003_stack (R := R)) (poolManagerCreation_block_12003_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12003_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12003) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_12003_stack (R := R)) (poolManagerCreation_block_12003_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12003 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12007_taken`. -/
def poolManagerCreation_block_12007_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12007. -/
theorem poolManagerCreation_block_12007_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 7857) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12007) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7857) (poolManagerCreation_block_12007_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 18) (C + ((59))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7857) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 7857) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7857)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12007_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 7857) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12007) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 7857) (poolManagerCreation_block_12007_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12007_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12007_fallthrough`. -/
def poolManagerCreation_block_12007_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12007. -/
theorem poolManagerCreation_block_12007_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12007) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12068) (poolManagerCreation_block_12007_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 18) (C + ((59))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7857) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12068)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12007_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12007) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12068) (poolManagerCreation_block_12007_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12007_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12068`. -/
def poolManagerCreation_block_12068_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `poolManagerCreation_block_12068`. -/
def poolManagerCreation_block_12068_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12068. -/
theorem poolManagerCreation_block_12068 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12068) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_12068_stack (R := R)) (poolManagerCreation_block_12068_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12068_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12068) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x1 (poolManagerCreation_block_12068_stack (R := R)) (poolManagerCreation_block_12068_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12068 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12072_taken`. -/
def poolManagerCreation_block_12072_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12072. -/
theorem poolManagerCreation_block_12072_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12072) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12072_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 164) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12072_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12072) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12072_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12072_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12072_fallthrough`. -/
def poolManagerCreation_block_12072_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12072. -/
theorem poolManagerCreation_block_12072_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12072) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12089) (poolManagerCreation_block_12072_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 164) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12089)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12072_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12072) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12089) (poolManagerCreation_block_12072_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12072_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12089`. -/
def poolManagerCreation_block_12089_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12089. -/
theorem poolManagerCreation_block_12089 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12089) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_12089_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x0 hvalid) (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12089_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x0 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12089) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x0 (poolManagerCreation_block_12089_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12089 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12090_taken`. -/
def poolManagerCreation_block_12090_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12090. -/
theorem poolManagerCreation_block_12090_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12090) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12090_taken_stack (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12090_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12090) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12090_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12090_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12090_fallthrough`. -/
def poolManagerCreation_block_12090_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 12090. -/
theorem poolManagerCreation_block_12090_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12090) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (poolManagerCreation_block_12090_fallthrough_stack (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12133)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12090_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt (x0 + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12090) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (poolManagerCreation_block_12090_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12090_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12133`. -/
def poolManagerCreation_block_12133_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 11960) :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12133. -/
theorem poolManagerCreation_block_12133 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 11794) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11794) (poolManagerCreation_block_12133_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11960) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11794) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11794) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11794)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12133_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 11794) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12133) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11794) (poolManagerCreation_block_12133_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12133 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12145_taken`. -/
def poolManagerCreation_block_12145_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12145. -/
theorem poolManagerCreation_block_12145_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12145) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12145_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12145_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12145) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12145_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12145_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12145_fallthrough`. -/
def poolManagerCreation_block_12145_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12145. -/
theorem poolManagerCreation_block_12145_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12145) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (poolManagerCreation_block_12145_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12179)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12145_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12145) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (poolManagerCreation_block_12145_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12145_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12179_taken`. -/
def poolManagerCreation_block_12179_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_12179_taken`. -/
def poolManagerCreation_block_12179_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12179. -/
theorem poolManagerCreation_block_12179_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12179_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12179_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((40) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12179_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12179_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12179_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12179_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12179_fallthrough`. -/
def poolManagerCreation_block_12179_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_12179_fallthrough`. -/
def poolManagerCreation_block_12179_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12179. -/
theorem poolManagerCreation_block_12179_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (poolManagerCreation_block_12179_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12179_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((40) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12213)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12179_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12179) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (poolManagerCreation_block_12179_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12179_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12179_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12213_taken`. -/
def poolManagerCreation_block_12213_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_12213_taken`. -/
def poolManagerCreation_block_12213_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12213. -/
theorem poolManagerCreation_block_12213_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12213_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12213_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12213_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12213_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12213_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12213_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12213_fallthrough`. -/
def poolManagerCreation_block_12213_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_12213_fallthrough`. -/
def poolManagerCreation_block_12213_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12213. -/
theorem poolManagerCreation_block_12213_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12233) (poolManagerCreation_block_12213_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12213_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((46) + (memExpansionCost aw (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 16777215) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12233)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12213_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 16777215))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12233) (poolManagerCreation_block_12213_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12213_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12213_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_12233_taken`. -/
def poolManagerCreation_block_12233_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `poolManagerCreation_block_12233_taken`. -/
def poolManagerCreation_block_12233_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (x1 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12233. -/
theorem poolManagerCreation_block_12233_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12233) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12233_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12233_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((48) + (memExpansionCost aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 100) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.signextend (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_12233_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12233) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_12233_taken_stack (ee := ee) (x1 := x1) (R := R)) (poolManagerCreation_block_12233_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_12233_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end poolManagerCreationBlocks
