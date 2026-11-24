import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperVault.Bytecode
import Tests.Pipeline.VyperVault.Immutables
import Tests.Pipeline.VyperVault.ImmutableCode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vyperVaultBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `vyperVault_block_385_fallthrough`. -/
def vyperVault_block_385_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 385. -/
theorem vyperVault_block_385_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 385) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 408) (vyperVault_block_385_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨385⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨386⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨387⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨388⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨389⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨391⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨392⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨394⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨395⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨397⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨398⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨399⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨400⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r14 := r13.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨401⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r15 := r14.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨402⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r16 := r15.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨403⟩ : UInt256), .LT, none)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨404⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r18 := r17.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨407⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 408)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_385_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 385) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 408) (vyperVault_block_385_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_385_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 408. -/
theorem vyperVault_block_408 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 408) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) x0) ByteArray.empty := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨408⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨409⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨410⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨411⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨412⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨414⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.caller (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨415⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 20644549604082266639320257001935285394590065917650136896563126397825491550916) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨416⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 20644549604082266639320257001935285394590065917650136896563126397825491550916), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨449⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨451⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨452⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r12 := RD.genMstore r11 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨454⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨455⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨457⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r15 := RD.genLog2 r14 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨459⟩ : UInt256), .LOG2, none)) hperm (by evm_ov)
  exact r15.stop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨460⟩ : UInt256), .STOP, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 461. -/
theorem vyperVault_block_461_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 461) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨461⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3363399026) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨462⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3363399026), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨467⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨468⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨469⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨472⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_461_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 461) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_461_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 461. -/
theorem vyperVault_block_461_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 461) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨461⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3363399026) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨462⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3363399026), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨467⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨468⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨469⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨472⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 473)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_461_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 461) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_461_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 473. -/
theorem vyperVault_block_473_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨473⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨474⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨477⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_473_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_473_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 473. -/
theorem vyperVault_block_473_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨473⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨474⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨477⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 478)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_473_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 473) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_473_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 478. -/
theorem vyperVault_block_478_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨478⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨479⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨480⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r4 := r3.eq (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨482⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨483⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨486⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_478_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_478_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 478. -/
theorem vyperVault_block_478_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 487) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨478⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨479⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨480⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r4 := r3.eq (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨482⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨483⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨486⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 487)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_478_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 478) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 487) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_478_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVault_block_487_taken`. -/
def vyperVault_block_487_taken_memory {immWords : String → UInt256} {mem : ByteArray} : ByteArray :=
  ((immWords "OWNER").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Vyper scalar immutable summary for block at pc 487. -/
theorem vyperVault_block_487_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (immWords "OWNER"))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 487) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 628) R (vyperVault_block_487_taken_memory (immWords := immWords) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  have hcode : Tests.Pipeline.VyperVault.vyperVaultBytecode.size = 1429 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "OWNER").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableCopyWord_OWNER immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "OWNER" := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableLoad_OWNER immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  have hcond_raw : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) ≠ (UInt256.ofNat 0) := by
    try simp only [hcopy0]
    try simp only [hload0]
    exact hcond
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨487⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨489⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨490⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨491⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1429) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨493⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1429), 2))) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨496⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨497⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨498⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genMload r8 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨499⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r10 := r9.caller (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨500⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r11 := r10.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨501⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r12 := r11.iszero (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨502⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 628) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨503⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 628), 2))) (by evm_ov)
  have r14 := r13.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨506⟩ : UInt256), .JUMPI, none)) hcond_raw hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 628)) r14 (by native_decide)
  have hraw := rFinal
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [vyperVault_block_487_taken_memory]
  exact ⟨_, _, hraw⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_487_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (immWords "OWNER"))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 487) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 628) R (vyperVault_block_487_taken_memory (immWords := immWords) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_487_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVault_block_487_fallthrough`. -/
def vyperVault_block_487_fallthrough_memory {immWords : String → UInt256} {mem : ByteArray} : ByteArray :=
  ((immWords "OWNER").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Vyper scalar immutable summary for block at pc 487. -/
theorem vyperVault_block_487_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (immWords "OWNER"))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 487) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 507) R (vyperVault_block_487_fallthrough_memory (immWords := immWords) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  have hcode : Tests.Pipeline.VyperVault.vyperVaultBytecode.size = 1429 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "OWNER").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableCopyWord_OWNER immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "OWNER" := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableLoad_OWNER immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  have hcond_raw : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) = (UInt256.ofNat 0) := by
    try simp only [hcopy0]
    try simp only [hload0]
    exact hcond
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨487⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨489⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨490⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨491⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1429) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨493⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1429), 2))) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨496⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨497⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨498⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genMload r8 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨499⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r10 := r9.caller (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨500⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r11 := r10.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨501⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r12 := r11.iszero (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨502⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 628) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨503⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 628), 2))) (by evm_ov)
  have r14 := r13.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨506⟩ : UInt256), .JUMPI, none)) hcond_raw (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 507)) r14 (by native_decide)
  have hraw := rFinal
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [vyperVault_block_487_fallthrough_memory]
  exact ⟨_, _, hraw⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_487_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (immWords "OWNER"))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 487) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 507) R (vyperVault_block_487_fallthrough_memory (immWords := immWords) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_487_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_507`. -/
def vyperVault_block_507_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: ((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: R)

/-- Final memory for bytecode block summary `vyperVault_block_507`. -/
def vyperVault_block_507_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 147028384).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 507. -/
theorem vyperVault_block_507 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 507) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 622) (vyperVault_block_507_stack (ee := ee) (mem := mem) (R := R)) (vyperVault_block_507_memory (ee := ee) (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((182) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) + (3 + 3 * (((UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨507⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨509⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨510⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨512⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 9) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨513⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 9), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨515⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨517⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨518⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨551⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨553⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨554⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r12 := r11.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨556⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨557⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨559⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨560⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r16 := RD.genMload r15 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨561⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r17 := r16.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨562⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r18 := RD.genMstore r17 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨563⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨564⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r20 := r19.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨566⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r21 := r20.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨567⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r22 := RD.genMload r21 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨568⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨569⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r24 := r23.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨571⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r25 := r24.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨572⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r26 := RD.genMstore r25 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨573⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r27 := r26.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨574⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r28 := RD.genMload r27 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨575⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r29 := r28.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨576⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨577⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r31 := r30.dup4 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨579⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r32 := r31.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨580⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r33 := r32.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨581⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨582⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r35 := r34.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨584⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r36 := r35.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨585⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r37 := r36.sub (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨586⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r38 := r37.and (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨587⟩ : UInt256), .AND, none)) (by evm_ov)
  have r39 := r38.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨588⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r40 := r39.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨589⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r41 := RD.genCalldatacopy r40 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨590⟩ : UInt256), .CALLDATACOPY, none)) (by evm_ov)
  have r42 := r41.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨591⟩ : UInt256), .POP, none)) (by evm_ov)
  have r43 := r42.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨592⟩ : UInt256), .POP, none)) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨593⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r45 := r44.not (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨595⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨596⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r47 := r46.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨598⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r48 := RD.genMload r47 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨599⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨600⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r50 := r49.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨602⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r51 := r50.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨603⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r52 := r51.and (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨604⟩ : UInt256), .AND, none)) (by evm_ov)
  have r53 := r52.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨605⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r54 := r53.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨606⟩ : UInt256), .POP, none)) (by evm_ov)
  have r55 := r54.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨607⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r56 := r55.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨608⟩ : UInt256), .POP, none)) (by evm_ov)
  have r57 := r56.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨609⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r58 := r57.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨610⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r59 := r58.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨611⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r60 := r59.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨612⟩ : UInt256), .POP, none)) (by evm_ov)
  have r61 := r60.push4 (UInt256.ofNat 147028384) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨613⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 147028384), 4))) (by evm_ov)
  have r62 := r61.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨618⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r63 := RD.genMstore r62 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨620⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r64 := r63.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨621⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 622)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_507_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 507) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 622) (vyperVault_block_507_stack (ee := ee) (mem := mem) (R := R)) (vyperVault_block_507_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_507 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 622. -/
theorem vyperVault_block_622 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 622) (x0 :: R) mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨622⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.add (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨624⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 156) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨625⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 156), 1))) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨627⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `vyperVault_block_628`. -/
def vyperVault_block_628_stack {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (immWords "OWNER") :: (memLoad (UInt256.ofNat 64) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R)

/-- Final memory for bytecode block summary `vyperVault_block_628`. -/
def vyperVault_block_628_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((immWords "OWNER").toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Vyper scalar immutable summary for block at pc 628. -/
theorem vyperVault_block_628 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 628) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 656) (vyperVault_block_628_stack (immWords := immWords) (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVault_block_628_memory (immWords := immWords) (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (⟨0⟩ : UInt256)) k' C' := by
  have hcode : Tests.Pipeline.VyperVault.vyperVaultBytecode.size = 1429 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "OWNER").toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableCopyWord_OWNER immWords (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "OWNER" := by
    simpa [hcode] using Tests.Pipeline.VyperVault.immutableLoad_OWNER immWords (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨628⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨629⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨631⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨632⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨634⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨635⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨636⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sstore r7 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨638⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r9 := r8.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨639⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r10 := r9.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨640⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := r10.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨641⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r12 := r11.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨642⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨643⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r14 := RD.genMload r13 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨645⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨646⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1429) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨648⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1429), 2))) (by evm_ov)
  have r17 := r16.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨651⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r18 := RD.genCodecopy r17 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨652⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r19 := r18.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨653⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨654⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨655⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 656)) r21 (by native_decide)
  have hraw := rFinal
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [vyperVault_block_628_stack, vyperVault_block_628_memory]
  exact ⟨_, _, hraw⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_628_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 628) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 656) (vyperVault_block_628_stack (immWords := immWords) (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVault_block_628_memory (immWords := immWords) (ee := ee) (mem := mem) (σ := σ)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_628 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 656: call (0xf1). No RD transition is asserted. Summaries resume at pc 657 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vyperVault_block_657_taken`. -/
def vyperVault_block_657_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 657. -/
theorem vyperVault_block_657_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 657) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_657_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨657⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨658⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨661⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_657_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 657) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_657_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_657_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_657_fallthrough`. -/
def vyperVault_block_657_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 657. -/
theorem vyperVault_block_657_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 657) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (vyperVault_block_657_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.iszero (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨657⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨658⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨661⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 662)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_657_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 657) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (vyperVault_block_657_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_657_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 662. -/
theorem vyperVault_block_662 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 3)) (mem.readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨662⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨664⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨666⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  have r4 := r3.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨668⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨669⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  exact RD.genRet r5 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨670⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 671. -/
theorem vyperVault_block_671_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 671) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨671⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨672⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 773487949), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨677⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨678⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨679⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨682⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_671_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 671) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_671_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 671. -/
theorem vyperVault_block_671_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 671) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨671⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨672⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 773487949), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨677⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨678⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨679⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨682⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 683)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_671_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 671) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_671_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 683. -/
theorem vyperVault_block_683_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨683⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨685⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨686⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨687⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨688⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨689⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨692⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_683_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_683_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 683. -/
theorem vyperVault_block_683_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨683⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨685⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨686⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨687⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨688⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨689⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨692⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 693)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_683_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 683) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_683_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 693. -/
theorem vyperVault_block_693_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨693⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨694⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨695⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r4 := r3.eq (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨697⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨698⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨701⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_693_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_693_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 693. -/
theorem vyperVault_block_693_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 702) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨693⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨694⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨695⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r4 := r3.eq (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨697⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨698⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨701⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 702)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_693_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 693) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 702) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_693_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVault_block_702_taken`. -/
def vyperVault_block_702_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 702. -/
theorem vyperVault_block_702_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 849) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 702) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 849) R (vyperVault_block_702_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨702⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨704⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨705⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨706⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r5 := r4.calldataload (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨708⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨709⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r7 := r6.caller (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨711⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨712⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨714⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨715⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := RD.genMstore r10 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨716⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨717⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r13 := r12.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨719⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨720⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨721⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r16 := r15.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨722⟩ : UInt256), .LT, none)) (by evm_ov)
  have r17 := r16.iszero (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨723⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 849) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨724⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 849), 2))) (by evm_ov)
  have r19 := r18.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨727⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 849)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_702_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 849) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 702) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 849) R (vyperVault_block_702_taken_memory (ee := ee) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_702_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vyperVaultBlocks
