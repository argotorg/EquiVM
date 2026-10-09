import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.UniswapV4PoolManager.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode

/-- Final stack for bytecode block summary `poolManagerCreation_block_22842`. -/
def poolManagerCreation_block_22842_stack {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight x3 (UInt256.ofNat 96)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22842. -/
theorem poolManagerCreation_block_22842 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22842) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x4 (poolManagerCreation_block_22842_stack (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x4 hvalid) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22842_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22842) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x4 (poolManagerCreation_block_22842_stack (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22842 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_22851_taken`. -/
def poolManagerCreation_block_22851_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) :: (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) :: x0 :: x1 :: (UInt256.shiftLeft x0 (UInt256.ofNat 96)) :: (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22851. -/
theorem poolManagerCreation_block_22851_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22851) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_22851_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 28) (C + ((94))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 79228162514264337593543950336) (width := 13) (op := .PUSH13) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22851_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22851) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_22851_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22851_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_22851_fallthrough`. -/
def poolManagerCreation_block_22851_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) :: (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) :: x0 :: x1 :: (UInt256.shiftLeft x0 (UInt256.ofNat 96)) :: (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22851. -/
theorem poolManagerCreation_block_22851_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22851) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (poolManagerCreation_block_22851_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 28) (C + ((94))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 79228162514264337593543950336) (width := 13) (op := .PUSH13) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22927)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22851_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96))) (UInt256.lt (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.shiftLeft x0 (UInt256.ofNat 96)))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22851) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (poolManagerCreation_block_22851_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22851_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_22927_taken`. -/
def poolManagerCreation_block_22927_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 22927. -/
theorem poolManagerCreation_block_22927_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22844) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22844) (poolManagerCreation_block_22927_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22844) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 22844) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22844)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22927_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22844) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22844) (poolManagerCreation_block_22927_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22927_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_22927_fallthrough`. -/
def poolManagerCreation_block_22927_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 22927. -/
theorem poolManagerCreation_block_22927_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22932) (poolManagerCreation_block_22927_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 22844) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22932)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22927_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22927) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22932) (poolManagerCreation_block_22927_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22927_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_22932`. -/
def poolManagerCreation_block_22932_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) x1) :: x2 :: x3 :: ((UInt256.div (UInt256.sub (⟨0⟩ : UInt256) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) + (UInt256.ofNat 1)) :: (UInt256.mulMod x0 (UInt256.ofNat 79228162514264337593543950336) x1) :: (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1) :: x2 :: (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x1 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x1) x1))) (UInt256.ofNat 2)))))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 22932. -/
theorem poolManagerCreation_block_22932 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22932) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23018) (poolManagerCreation_block_22932_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 64) (C + ((225))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.pushConst (UInt256.ofNat 79228162514264337593543950336) (width := 13) (op := .PUSH13) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23018)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_22932_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22932) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23018) (poolManagerCreation_block_22932_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_22932 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23018`. -/
def poolManagerCreation_block_23018_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.lor (UInt256.div (UInt256.sub x6 x4) x5) (UInt256.mul (UInt256.sub x2 (UInt256.gt x0 x1)) x3)) x7) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23018. -/
theorem poolManagerCreation_block_23018 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23018) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x8 (poolManagerCreation_block_23018_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 11) (C + ((44))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x8 hvalid) (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23018_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23018) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x8 (poolManagerCreation_block_23018_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23018 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23029`. -/
def poolManagerCreation_block_23029_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x2 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23029. -/
theorem poolManagerCreation_block_23029 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23029) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x4 (poolManagerCreation_block_23029_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x4 hvalid) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23029_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23029) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x4 (poolManagerCreation_block_23029_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23029 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23036_taken`. -/
def poolManagerCreation_block_23036_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) :: (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) :: x0 :: x1 :: x2 :: (UInt256.mul x0 x1) :: (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23036. -/
theorem poolManagerCreation_block_23036_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x2 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23036) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_23036_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 28) (C + ((96))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 816) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23036_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x2 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23036) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 816) (poolManagerCreation_block_23036_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23036_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23036_fallthrough`. -/
def poolManagerCreation_block_23036_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) :: (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) :: x0 :: x1 :: x2 :: (UInt256.mul x0 x1) :: (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23036. -/
theorem poolManagerCreation_block_23036_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x2 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23036) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (poolManagerCreation_block_23036_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 28) (C + ((96))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 816) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23098)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23036_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x2 (UInt256.sub (UInt256.sub (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1)) (UInt256.lt (UInt256.mulMod x0 x1 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (UInt256.mul x0 x1))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23036) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (poolManagerCreation_block_23036_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23036_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23098_taken`. -/
def poolManagerCreation_block_23098_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23098. -/
theorem poolManagerCreation_block_23098_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 23002) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23002) (poolManagerCreation_block_23098_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 23002) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 23002) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23002)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23098_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 23002) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23002) (poolManagerCreation_block_23098_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23098_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23098_fallthrough`. -/
def poolManagerCreation_block_23098_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 23098. -/
theorem poolManagerCreation_block_23098_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23103) (poolManagerCreation_block_23098_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 23002) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23103)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23098_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq x0 x1) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23098) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23103) (poolManagerCreation_block_23098_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23098_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23103`. -/
def poolManagerCreation_block_23103_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mulMod x0 x1 x2) :: x3 :: x4 :: ((UInt256.div (UInt256.sub (⟨0⟩ : UInt256) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) + (UInt256.ofNat 1)) :: (UInt256.mulMod x0 x1 x2) :: (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2) :: x3 :: (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2))))) (UInt256.mul (UInt256.sub (UInt256.ofNat 2) (UInt256.mul (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2)) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))) (UInt256.xor (UInt256.mul (UInt256.ofNat 3) (UInt256.div x2 (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) x2) x2))) (UInt256.ofNat 2)))))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23103. -/
theorem poolManagerCreation_block_23103 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23103) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23176) (poolManagerCreation_block_23103_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 64) (C + ((225))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23176)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23103_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23103) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23176) (poolManagerCreation_block_23103_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23103 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23176`. -/
def poolManagerCreation_block_23176_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.lor (UInt256.div (UInt256.sub x6 x4) x5) (UInt256.mul (UInt256.sub x2 (UInt256.gt x0 x1)) x3)) x7) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23176. -/
theorem poolManagerCreation_block_23176 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23176) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x8 (poolManagerCreation_block_23176_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 11) (C + ((44))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x8 hvalid) (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23176_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x8 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23176) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x8 (poolManagerCreation_block_23176_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23176 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23187`. -/
def poolManagerCreation_block_23187_stack {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x3 x2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23187. -/
theorem poolManagerCreation_block_23187 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23187) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x5 (poolManagerCreation_block_23187_stack (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x5 hvalid) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23187_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23187) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x5 (poolManagerCreation_block_23187_stack (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23187 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23195`. -/
def poolManagerCreation_block_23195_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x2 (UInt256.ofNat 340282366920938463463374607431768211455)) :: (UInt256.xor ((UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) + (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) :: (UInt256.ofNat 23092) :: (UInt256.xor ((UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) + (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) :: (UInt256.ofNat 79228162514264337593543950336) :: (UInt256.ofNat 1) :: (UInt256.land x2 (UInt256.ofNat 340282366920938463463374607431768211455)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23195. -/
theorem poolManagerCreation_block_23195 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22544) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22544) (poolManagerCreation_block_23195_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 27) (C + ((84))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 79228162514264337593543950336) (width := 13) (op := .PUSH13) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.sar (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 23092) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 22544) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 22544) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22544)) r27 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23195_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22544) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22544) (poolManagerCreation_block_23195_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23195 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23277`. -/
def poolManagerCreation_block_23277_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.mulMod x4 x1 x2))) x3) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23277. -/
theorem poolManagerCreation_block_23277 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23277) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x5 (poolManagerCreation_block_23277_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 9) (C + ((35))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.mulmod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x5 hvalid) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23277_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains x5 = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23277) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 x5 (poolManagerCreation_block_23277_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23277 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23286`. -/
def poolManagerCreation_block_23286_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x2 (UInt256.ofNat 340282366920938463463374607431768211455)) :: (UInt256.xor ((UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) + (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))) (UInt256.sar (UInt256.ofNat 255) (UInt256.sub (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))))) :: (UInt256.ofNat 13903) :: R)

/-- Automatically generated RD summary for bytecode block at pc 23286. -/
theorem poolManagerCreation_block_23286 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22544) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23286) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22544) (poolManagerCreation_block_23286_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 23) (C + ((72))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 13903) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.sar (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 22544) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 22544) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22544)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23286_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 22544) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23286) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 22544) (poolManagerCreation_block_23286_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23286 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23350_taken`. -/
def poolManagerCreation_block_23350_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 23350. -/
theorem poolManagerCreation_block_23350_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 23342) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23342) (poolManagerCreation_block_23350_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 23342) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 23342) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23342)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23350_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode 0).contains (UInt256.ofNat 23342) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23342) (poolManagerCreation_block_23350_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23350_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManagerCreation_block_23350_fallthrough`. -/
def poolManagerCreation_block_23350_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 23350. -/
theorem poolManagerCreation_block_23350_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23403) (poolManagerCreation_block_23350_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode.size = 24194 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 23342) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManagerCreation_block_23350_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.land x1 (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23350) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.poolManagerCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 23403) (poolManagerCreation_block_23350_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManagerCreation_block_23350_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end poolManagerCreationBlocks
