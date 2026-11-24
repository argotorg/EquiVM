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

/-- Final stack for bytecode block summary `vyperVault_block_1292_taken`. -/
def vyperVault_block_1292_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1292. -/
theorem vyperVault_block_1292_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_1292_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1292⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1294⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1295⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1296⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1298⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1299⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1302⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1292_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_1292_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1292_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_1292_fallthrough`. -/
def vyperVault_block_1292_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1292. -/
theorem vyperVault_block_1292_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1303) (vyperVault_block_1292_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1292⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1294⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1295⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1296⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1298⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1299⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1302⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1303)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1292_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1303) (vyperVault_block_1292_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1292_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_1303`. -/
def vyperVault_block_1303_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `vyperVault_block_1303`. -/
def vyperVault_block_1303_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1303. -/
theorem vyperVault_block_1303 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1303) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1321) (vyperVault_block_1303_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vyperVault_block_1303_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1303⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1305⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1306⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1308⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r5 := RD.genMload r4 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1310⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1311⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1313⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1314⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1315⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1316⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := r10.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1318⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1319⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1320⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1321)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1303_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1303) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1321) (vyperVault_block_1303_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vyperVault_block_1303_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVault_block_1303 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1321: unsupported_47 (0x47). No RD transition is asserted. Summaries resume at pc 1322 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 1322. -/
theorem vyperVault_block_1322 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1322) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 σ (((UInt256.xor (UInt256.mul (UInt256.lt x1 x0) (UInt256.xor x0 x1)) x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32).readWithPadding (UInt256.ofNat 96).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1322⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r2 := r1.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1323⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1324⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1325⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.dup3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1326⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r6 := r5.dup5 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1327⟩ : UInt256), .DUP5, none)) (by evm_ov)
  have r7 := r6.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1328⟩ : UInt256), .LT, none)) (by evm_ov)
  have r8 := r7.mul (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1329⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r9 := r8.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1330⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r10 := r9.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1331⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r11 := r10.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1332⟩ : UInt256), .POP, none)) (by evm_ov)
  have r12 := r11.swap1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1333⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r13 := r12.pop (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1334⟩ : UInt256), .POP, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1335⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1337⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1338⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1340⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  exact RD.genRet r17 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1342⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1343. -/
theorem vyperVault_block_1343_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2106073239)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1343) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1343⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2106073239) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1344⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2106073239), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1349⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1350⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1351⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1354⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1343_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2106073239)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1343) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1343_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1343. -/
theorem vyperVault_block_1343_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2106073239)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1343) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1343⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2106073239) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1344⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2106073239), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1349⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1350⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1351⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1354⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1355)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1343_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2106073239)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1343) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1343_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1355. -/
theorem vyperVault_block_1355_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1355⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1356⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1359⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1355_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1355_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1355. -/
theorem vyperVault_block_1355_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1360) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1355⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1356⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1359⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1360)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1355_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1355) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1360) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1355_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1360. -/
theorem vyperVault_block_1360 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1360) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1360⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1362⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1363⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1365⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1366⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1368⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  exact RD.genRet r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1370⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1371. -/
theorem vyperVault_block_1371_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1371) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1371⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4033993562) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1372⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 4033993562), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1377⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1378⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1379⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1382⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1371_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1371) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1371_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1371. -/
theorem vyperVault_block_1371_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1371) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1371⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4033993562) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1372⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 4033993562), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1377⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1378⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1379⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1382⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1383)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1371_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1371) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1371_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1383. -/
theorem vyperVault_block_1383_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1383⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1384⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1387⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1383_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1383_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1383. -/
theorem vyperVault_block_1383_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1388) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1383⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1384⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1387⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1388)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1383_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1383) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1388) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1383_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1388. -/
theorem vyperVault_block_1388 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1388) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1388⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1390⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1391⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1393⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1394⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1396⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  exact RD.genRet r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1398⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1399. -/
theorem vyperVault_block_1399 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1399⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1400⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1401⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1402⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1403. -/
theorem vyperVault_block_1403 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1403⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1404⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1405⟩ : UInt256), .DUP1, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1406⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `vyperVault_block_1407`. -/
def vyperVault_block_1407_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sdiv x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1407. -/
theorem vyperVault_block_1407 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1407) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1408) (vyperVault_block_1407_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((5))) := by
  let r0 := h
  have r1 := r0.sdiv (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1407⟩ : UInt256), .SDIV, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1408)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1407_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1407) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1408) (vyperVault_block_1407_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1407 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1408: push24 (0x77). No RD transition is asserted. -/

end vyperVaultBlocks
