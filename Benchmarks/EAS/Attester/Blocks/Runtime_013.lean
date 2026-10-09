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

/-- Final stack for bytecode block summary `attesterRuntime_block_3624`. -/
def attesterRuntime_block_3624_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3631) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3624. -/
theorem attesterRuntime_block_3624 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2696) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3631) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3624⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3631), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2696) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3627⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2696), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3630⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2696)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3624_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2696) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3624 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_taken`. -/
def attesterRuntime_block_3631_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3706) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3631⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3632⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3633⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3635⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3636⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3638⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3639⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 63) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3672⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 63), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3674⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3675⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3676⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3677⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3678⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3679⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3680⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3681⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3682⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3691⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3692⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.or (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3693⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3694⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 3706) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3695⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3706), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3698⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3706)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3706) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_fallthrough`. -/
def attesterRuntime_block_3631_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3631⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3632⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3633⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3635⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3636⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3638⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3639⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 63) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3672⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 63), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3674⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3675⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3676⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3677⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3678⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3679⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3680⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3681⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3682⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3691⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3692⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.or (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3693⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3694⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 3706) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3695⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3706), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3698⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3699)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3699`. -/
def attesterRuntime_block_3699_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3706) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3699. -/
theorem attesterRuntime_block_3699 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2696) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3706) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3699⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3706), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2696) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3702⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2696), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3705⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2696)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3699_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 2696) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3699 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3736) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3706⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3707⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3709⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3710⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3711⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3712⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3713⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3715⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3716⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3717⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3718⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3719⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3720⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3721⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3722⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3723⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3724⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3725⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3726⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3727⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3736) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3728⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3736), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3731⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3736)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3736) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3706⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3707⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3709⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3710⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3711⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3712⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3713⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3715⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3716⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3717⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3718⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3719⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3720⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3721⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3722⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3723⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup8 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3724⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3725⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.gt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3726⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3727⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3736) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3728⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3736), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3731⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3732)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3732. -/
theorem attesterRuntime_block_3732 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3732⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3734⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3735⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3736`. -/
def attesterRuntime_block_3736_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: (x4 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3736. -/
theorem attesterRuntime_block_3736 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 6) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3736⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3737⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3739⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3740⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3741⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3742⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3743)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3736_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3736 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3771) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3743⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3744⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3745⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3746⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3747⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3771) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3748⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3771), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3751⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3771)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3771) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3743⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3744⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3745⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3746⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3747⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3771) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3748⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3771), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3751⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3752)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: (memLoad x4 mem) :: x3 :: ((UInt256.ofNat 32) + x4) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  ((memLoad x4 mem).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3752. -/
theorem attesterRuntime_block_3752 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((52) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3752⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3753⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3754⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3755⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3756⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3759⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3760⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3761⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3762⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3763⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3764⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3765⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3766⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 3743) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3767⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3743), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3770⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3743)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3752_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3743) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3752 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3771`. -/
def attesterRuntime_block_3771_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3771. -/
theorem attesterRuntime_block_3771 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3771⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3772⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap7 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3773⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap6 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3774⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3775⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3776⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3777⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3778⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3779⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3780⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3781⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3771_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3771 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (x0 + (UInt256.ofNat 96)) :: (UInt256.ofNat 3819) :: (memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) (x0 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3782. -/
theorem attesterRuntime_block_3782 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3109) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((84) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3782⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3783⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3785⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3786⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3787⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3788⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3789⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3791⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3792⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3793⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3794⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3796⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3798⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3799⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMload r14 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3800⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3801⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3803⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3804⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3805⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3806⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3819) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3807⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3819), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3810⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3812⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.add (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3813⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3814⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 3109) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3815⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3109), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3818⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3109)) r27 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3782_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3109) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3782 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3819`. -/
def attesterRuntime_block_3819_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3819. -/
theorem attesterRuntime_block_3819 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3819⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3820⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap4 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3821⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3822⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3823⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3824⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3825⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3826⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3819_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3819 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_taken`. -/
def attesterRuntime_block_3827_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3845) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3827⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3828⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3830⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3832⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3833⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3834⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3835⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3836⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3845) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3837⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3845), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3840⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3845)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains (UInt256.ofNat 3845) = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_fallthrough`. -/
def attesterRuntime_block_3827_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3827⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3828⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3830⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3832⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3833⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3834⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3835⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3836⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3845) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3837⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3845), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3840⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3841)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3841. -/
theorem attesterRuntime_block_3841 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3841⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3843⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3844⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3845`. -/
def attesterRuntime_block_3845_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3845. -/
theorem attesterRuntime_block_3845 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((22) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3845⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3846⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3847⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3848⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3849⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3850⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3851⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3845_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3845 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3852. -/
theorem attesterRuntime_block_3852 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3852) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  exact RD.invalid r0 (by immutable_decode(Benchmarks.EAS.Attester.Immutables.immutableLayout, Benchmarks.EAS.Attester.attesterBytecode, immWords, (⟨3852⟩ : UInt256), UInt8.ofNat 254, .INVALID, none, immutableLayout_inBounds, immutableTemplate_size64))

end attesterRuntimeBlocks
