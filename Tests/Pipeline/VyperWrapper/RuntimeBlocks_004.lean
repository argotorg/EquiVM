import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperWrapper.Bytecode
import Tests.Pipeline.VyperWrapper.Immutables
import Tests.Pipeline.VyperWrapper.ImmutableCode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace wrapperBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `wrapper_block_833_taken`. -/
def wrapper_block_833_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 833. -/
theorem wrapper_block_833_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 844) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 833) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 844) (wrapper_block_833_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 844) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨833⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 844), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨836⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 844)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_833_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 844) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 833) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 844) (wrapper_block_833_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_833_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_833_fallthrough`. -/
def wrapper_block_833_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 833. -/
theorem wrapper_block_833_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 833) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 837) (wrapper_block_833_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 844) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨833⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 844), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨836⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 837)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_833_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 833) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 837) (wrapper_block_833_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_833_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 837. -/
theorem wrapper_block_837 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 837) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨837⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨838⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨839⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨840⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨841⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨842⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨843⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_844`. -/
def wrapper_block_844_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 844. -/
theorem wrapper_block_844 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 844) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 846) (wrapper_block_844_stack (R := R)) mem aw rdata σ (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨844⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨845⟩ : UInt256), .POP, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 846)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_844_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 844) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 846) (wrapper_block_844_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_844 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 846. -/
theorem wrapper_block_846 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 846) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ (((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32).readWithPadding (UInt256.ofNat 96).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨846⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨847⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 32115547371186163167665232851642580405598206436585934868468754706858941601788) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨848⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 32115547371186163167665232851642580405598206436585934868468754706858941601788), 32))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨881⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r5 := RD.genMload r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨883⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨884⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨886⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨887⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨889⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r10 := RD.genLog2 r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨891⟩ : UInt256), .LOG2, none)) hperm (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨892⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨894⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  exact RD.genRet r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨896⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 897. -/
theorem wrapper_block_897_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3725498942)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1486) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 897) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨897⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3725498942) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨898⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3725498942), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨903⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨904⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1486) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨905⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1486), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨908⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1486)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_897_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3725498942)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1486) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 897) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_897_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 897. -/
theorem wrapper_block_897_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3725498942)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 897) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨897⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3725498942) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨898⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3725498942), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨903⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨904⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1486) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨905⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1486), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨908⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 909)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_897_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3725498942)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 897) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_897_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 909. -/
theorem wrapper_block_909_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨909⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨911⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨912⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨913⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨914⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨915⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨918⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_909_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_909_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 909. -/
theorem wrapper_block_909_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨909⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨911⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨912⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨913⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨914⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨915⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨918⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 919)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_909_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 909) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_909_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `wrapper_block_919_taken`. -/
def wrapper_block_919_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 919. -/
theorem wrapper_block_919_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1053) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1053) R (wrapper_block_919_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨919⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨921⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨922⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r4 := r3.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨924⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨925⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨927⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨928⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r8 := RD.genMstore r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨929⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨930⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := r9.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨932⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨933⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨934⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r13 := r12.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨935⟩ : UInt256), .LT, none)) (by evm_ov)
  have r14 := r13.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨936⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1053) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨937⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1053), 2))) (by evm_ov)
  have r16 := r15.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨940⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1053)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_919_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1053) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1053) R (wrapper_block_919_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_919_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `wrapper_block_919_fallthrough`. -/
def wrapper_block_919_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 919. -/
theorem wrapper_block_919_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 941) R (wrapper_block_919_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨919⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨921⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨922⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r4 := r3.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨924⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨925⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨927⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨928⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r8 := RD.genMstore r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨929⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨930⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := r9.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨932⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨933⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨934⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r13 := r12.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨935⟩ : UInt256), .LT, none)) (by evm_ov)
  have r14 := r13.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨936⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1053) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨937⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1053), 2))) (by evm_ov)
  have r16 := r15.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨940⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 941)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_919_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 919) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 941) R (wrapper_block_919_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_919_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 941. -/
theorem wrapper_block_941 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 941) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨941⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨943⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨944⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨946⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 12) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨947⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 12), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨949⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨951⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨952⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨985⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨987⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨988⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r12 := r11.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨990⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨991⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨993⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 44) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨994⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 44), 1))) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨996⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨997⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r18 := RD.genMcopy r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨998⟩ : UInt256), .MCOPY, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨999⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1000⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1001⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1002⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r23 := r22.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1004⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r24 := r23.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1005⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r25 := r24.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1006⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1007⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r27 := r26.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1009⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r28 := r27.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1010⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r29 := r28.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1011⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r30 := r29.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1012⟩ : UInt256), .AND, none)) (by evm_ov)
  have r31 := r30.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1013⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r32 := r31.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1014⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1015⟩ : UInt256), .CALLDATACOPY, none)) (by evm_ov)
  have r34 := r33.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1016⟩ : UInt256), .POP, none)) (by evm_ov)
  have r35 := r34.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1017⟩ : UInt256), .POP, none)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1018⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r37 := r36.not (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1020⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1021⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r39 := r38.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1023⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r40 := RD.genMload r39 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1024⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1025⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r42 := r41.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1027⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r43 := r42.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1028⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r44 := r43.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1029⟩ : UInt256), .AND, none)) (by evm_ov)
  have r45 := r44.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1030⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r46 := r45.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1031⟩ : UInt256), .POP, none)) (by evm_ov)
  have r47 := r46.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1032⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r48 := r47.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1033⟩ : UInt256), .POP, none)) (by evm_ov)
  have r49 := r48.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1034⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r50 := r49.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1035⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r51 := r50.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1036⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r52 := r51.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1037⟩ : UInt256), .POP, none)) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1038⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 147028384), 4))) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1043⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r55 := RD.genMstore r54 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1045⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r56 := r55.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1046⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1047⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r58 := r57.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1049⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 156) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1050⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 156), 1))) (by evm_ov)
  exact RD.genRev r59 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1052⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_1053`. -/
def wrapper_block_1053_stack {immWords : String → UInt256} {g : Sat256} {aw : UInt256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (immWords "TOKEN") :: (UInt256.ofNat 124) :: (UInt256.ofNat 36) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (immWords "TOKEN") :: R)

/-- Final memory for bytecode block summary `wrapper_block_1053`. -/
def wrapper_block_1053_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)

/-- Vyper scalar immutable summary for block at pc 1053. -/
theorem wrapper_block_1053 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1053) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1085) (wrapper_block_1053_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_1053_memory (immWords := immWords) (ee := ee) (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableCopyWord_TOKEN immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "TOKEN" := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableLoad_TOKEN immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1053⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1054⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1056⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r4 := r3.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1059⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r5 := RD.genCodecopy r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1060⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1061⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1062⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 1889567281) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1063⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1889567281), 4))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1068⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1070⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.address (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1071⟩ : UInt256), .ADDRESS, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1072⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1074⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1075⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1077⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1079⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 124) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1081⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 124), 1))) (by evm_ov)
  have r18 := r17.dup5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1083⟩ : UInt256), .DUP5, none)) (by evm_ov)
  have r19 := RD.genGas (RD.normalizeCounters (k' := k + 18) (C' := C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) r18 (by omega) (by omega)) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1084⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1085)) r19 (by native_decide)
  have hraw : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1085) (((g.subNat (C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: (UInt256.ofNat 124) :: (UInt256.ofNat 36) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
    exact RD.normalizeCounters rFinal (by omega) (by omega)
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [wrapper_block_1053_stack, wrapper_block_1053_memory]
  exact hraw

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1053_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1053) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1085) (wrapper_block_1053_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_1053_memory (immWords := immWords) (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1053 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1085: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 1086 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_1086_taken`. -/
def wrapper_block_1086_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1086. -/
theorem wrapper_block_1086_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1097) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1086) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) (wrapper_block_1086_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1097) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1086⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1097), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1089⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1097)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1086_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1097) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1086) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) (wrapper_block_1086_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1086_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1086_fallthrough`. -/
def wrapper_block_1086_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1086. -/
theorem wrapper_block_1086_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1086) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1090) (wrapper_block_1086_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1097) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1086⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1097), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1089⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1090)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1086_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1086) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1090) (wrapper_block_1086_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1086_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1090. -/
theorem wrapper_block_1090 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1090) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1090⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1091⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1092⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1093⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1094⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1095⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1096⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1097. -/
theorem wrapper_block_1097_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1097⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1098⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1100⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1101⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1102⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1105⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1097_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1097_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1097. -/
theorem wrapper_block_1097_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1097⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1098⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1100⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1101⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1102⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1105⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1106)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1097_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1097) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1097_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1106_taken`. -/
def wrapper_block_1106_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1106_taken`. -/
def wrapper_block_1106_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1106. -/
theorem wrapper_block_1106_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1106_taken_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1106_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((82) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1106⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1108⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1109⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1110⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1111⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1113⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1114⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1116⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1117⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1119⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1120⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1121⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1122⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r14 := r13.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1123⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1124⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1125⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r17 := r16.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1126⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r18 := r17.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1127⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r19 := r18.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1128⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r20 := r19.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1129⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r21 := r20.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1130⟩ : UInt256), .OR, none)) (by evm_ov)
  have r22 := r21.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1131⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1132⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r24 := r23.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1135⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1106_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1106_taken_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1106_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1106_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1106_fallthrough`. -/
def wrapper_block_1106_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1106_fallthrough`. -/
def wrapper_block_1106_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1106. -/
theorem wrapper_block_1106_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (wrapper_block_1106_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1106_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((82) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1106⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1108⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1109⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1110⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1111⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1113⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1114⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1116⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1117⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1119⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1120⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1121⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1122⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r14 := r13.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1123⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1124⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1125⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r17 := r16.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1126⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r18 := r17.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1127⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r19 := r18.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1128⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r20 := r19.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1129⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r21 := r20.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1130⟩ : UInt256), .OR, none)) (by evm_ov)
  have r22 := r21.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1131⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1132⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r24 := r23.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1135⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1136)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1106_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1106) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (wrapper_block_1106_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1106_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1106_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1136_taken`. -/
def wrapper_block_1136_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1136. -/
theorem wrapper_block_1136_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1136_taken_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1136⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1137⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1138⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1139⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1140⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1142⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r7 := r6.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1143⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r8 := r7.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1144⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1145⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r10 := r9.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1148⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1136_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1136_taken_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1136_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end wrapperBlocks
