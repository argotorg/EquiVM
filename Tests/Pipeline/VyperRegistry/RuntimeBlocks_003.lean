import Reasoning.Reach
import Tests.Pipeline.VyperRegistry.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace registryBlocks

/-- Automatically generated RD summary for bytecode block at pc 442. -/
theorem registry_block_442_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 442) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 450) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 569) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 450)) r5 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_442_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 442) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 450) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_442_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 450. -/
theorem registry_block_450 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 450) R mem aw rdata σ k C)
    : RDrev fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 45876960172658190342144148071268285734312574359075388889094533489066355195904) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 37) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := RD.genMcopy r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.push0 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.calldatasize (by native_decide) (by evm_ov)
  have r32 := r31.dup3 (by native_decide) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.pop (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r37 := r36.not (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r39 := r38.dup3 (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.and (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.pop (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.pop (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.pop (by native_decide) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by native_decide) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r58 := r57.add (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 348) (by native_decide) (by evm_ov)
  exact RD.genRev r59 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `registry_block_569_taken`. -/
def registry_block_569_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 569. -/
theorem registry_block_569_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 569) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_569_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_569_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 569) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_569_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_569_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_569_fallthrough`. -/
def registry_block_569_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 569. -/
theorem registry_block_569_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 569) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (registry_block_569_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 581)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_569_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 569) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (registry_block_569_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_569_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_581_taken`. -/
def registry_block_581_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `registry_block_581_taken`. -/
def registry_block_581_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem registry_block_581_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 666) (registry_block_581_taken_stack (R := R)) (registry_block_581_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  let r0 := h
  have r1 := r0.sub (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by native_decide) (by evm_ov)
  have r29 := r28.iszero (by native_decide) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 666) (by native_decide) (by evm_ov)
  have r31 := r30.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 666)) r31 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_581_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 666) (registry_block_581_taken_stack (R := R)) (registry_block_581_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_581_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_581_fallthrough`. -/
def registry_block_581_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `registry_block_581_fallthrough`. -/
def registry_block_581_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem registry_block_581_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) (registry_block_581_fallthrough_stack (R := R)) (registry_block_581_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  let r0 := h
  have r1 := r0.sub (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by native_decide) (by evm_ov)
  have r29 := r28.iszero (by native_decide) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 666) (by native_decide) (by evm_ov)
  have r31 := r30.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 624)) r31 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_581_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) (registry_block_581_fallthrough_stack (R := R)) (registry_block_581_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_581_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_624_taken`. -/
def registry_block_624_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registry_block_624_taken`. -/
def registry_block_624_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 624. -/
theorem registry_block_624_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_624_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_624_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.dup2 (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_624_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_624_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_624_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_624_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_624_fallthrough`. -/
def registry_block_624_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registry_block_624_fallthrough`. -/
def registry_block_624_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 624. -/
theorem registry_block_624_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 659) (registry_block_624_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_624_fallthrough_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.dup2 (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 659)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_624_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 659) (registry_block_624_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_624_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_624_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_659`. -/
def registry_block_659_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 659. -/
theorem registry_block_659 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 659) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 666) (registry_block_659_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 20) x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 666)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_659_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 659) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 666) (registry_block_659_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 20) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_659 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 666. -/
theorem registry_block_666 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 666) R mem aw rdata σ k C)
    : RDret fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)) (((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (UInt256.ofNat 256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sstore r18 hperm (by native_decide) (by evm_ov)
  have r20 := r19.push0 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sstore r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.pop (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  exact RD.genRet r27 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 704. -/
theorem registry_block_704_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 736) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 704) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1143006342) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 736)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_704_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 736) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 704) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_704_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 704. -/
theorem registry_block_704_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 704) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1143006342) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 716)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_704_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 704) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_704_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 716. -/
theorem registry_block_716_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_716_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_716_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 716. -/
theorem registry_block_716_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 726) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 726)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_716_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 716) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 726) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_716_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `registry_block_726`. -/
def registry_block_726_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 726. -/
theorem registry_block_726 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 793) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 726) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R (registry_block_726_memory (mem := mem)) (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 793) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 793)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_726_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 793) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 726) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R (registry_block_726_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_726 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 736. -/
theorem registry_block_736_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1639501452)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1639501452) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1533)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_736_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1639501452)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_736_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 736. -/
theorem registry_block_736_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1639501452)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1639501452) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 748)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_736_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1639501452)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_736_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 748. -/
theorem registry_block_748_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_748_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_748_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 748. -/
theorem registry_block_748_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 753) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 753)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_748_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 748) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 753) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_748_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 753. -/
theorem registry_block_753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 753) R mem aw rdata σ k C)
    : RDret fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r6 (by native_decide) (by evm_ov)

end registryBlocks
