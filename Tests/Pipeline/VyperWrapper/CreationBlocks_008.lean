import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperWrapper.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace wrapperCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperWrapper.wrapperCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperWrapper.wrapperCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 1798. -/
theorem wrapperCreation_block_1798_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1798) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1803) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1760) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1803)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapperCreation_block_1798_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1798) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1803) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapperCreation_block_1798_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1803. -/
theorem wrapperCreation_block_1803 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1803) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1814. -/
theorem wrapperCreation_block_1814 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1814) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1818. -/
theorem wrapperCreation_block_1818 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1818) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1822. -/
theorem wrapperCreation_block_1822 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1822) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) g s0 σ ByteArray.empty := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  exact r0.stop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/- Unsupported instruction boundary at pc 1823: unsupported_d5 (0xd5). No RD transition is asserted. Summaries resume at pc 1824 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapperCreation_block_1824`. -/
def wrapperCreation_block_1824_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mod x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1824. -/
theorem wrapperCreation_block_1824 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1824) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1825) (wrapperCreation_block_1824_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((5))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.mod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1825)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapperCreation_block_1824_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1824) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1825) (wrapperCreation_block_1824_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapperCreation_block_1824 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1825: unsupported_c0 (0xc0). No RD transition is asserted. Summaries resume at pc 1826 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapperCreation_block_1826`. -/
def wrapperCreation_block_1826_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mod (UInt256.ofNat 6762941518709633) (UInt256.mod x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1826. -/
theorem wrapperCreation_block_1826 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1837) (wrapperCreation_block_1826_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((13))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperWrapper.wrapperCreationBytecode.size = 1838 := by native_decide
  have r1 := r0.mod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 6762941518709633) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.mod (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1837)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapperCreation_block_1826_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1826) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1837) (wrapperCreation_block_1826_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapperCreation_block_1826 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1837: unsupported_dc (0xdc). No RD transition is asserted. -/

end wrapperCreationBlocks
